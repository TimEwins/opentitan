// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"

enum {
  /* Log2 of the number of bytes in an AES block. */
  kAesBlockLog2NumBytes = 4,
};
OT_ASSERT_ENUM_VALUE(kAesBlockNumBytes, 1 << kAesBlockLog2NumBytes);

/**
 * Precomputed modular reduction constants for Galois field multiplication.
 *
 * This implementation uses 4-bit windows. The bytes here represent 12-bit
 * little-endian values.
 *
 * The entry with index i in this table is equal to i * 0xe1, where the bytes i
 * and 0xe1 are interpreted as polynomials in the GCM Galois field. For
 * example, 0xe1 = 0b1110_0001 is the degree-8 polynomial x^8 + x^2 + x + 1.
 *
 * The field modulus for GCM is 2^128 + x^8 + x^2 + x + 1. Therefore, if a
 * field element is shifted, it can be reduced by multiplying the high bits
 * (128 and above) by 0xe1 and adding them to the low bits.
 *
 * There is a size/speed tradeoff in window size. For 8-bit windows, GHASH
 * becomes significantly faster, but the overhead for computing the product
 * table of a given hash subkey becomes higher, so larger windows are slower
 * for smaller inputs but faster for large inputs.
 */
static const uint16_t kGFReduceTable[16] = {
    0x0000, 0x201c, 0x4038, 0x6024, 0x8070, 0xa06c, 0xc048, 0xe054,
    0x00e1, 0x20fd, 0x40d9, 0x60c5, 0x8091, 0xa08d, 0xc0a9, 0xe0b5};

/**
 * Product table for a given hash subkey.
 *
 * See `make_product_table`.
 */
typedef struct aes_gcm_product_table {
  aes_block_t products[16];
} aes_gcm_product_table_t;

/**
 * Performs a bitwise XOR of two blocks.
 *
 * This operation corresponds to addition in the Galois field.
 *
 * @param x First operand block
 * @param y Second operand block
 * @param out Buffer in which to store output; can be the same as one or both
 * operands.
 */
static inline void block_xor(const aes_block_t *x, const aes_block_t *y,
                             aes_block_t *out) {
  for (size_t i = 0; i < kAesBlockNumWords; ++i) {
    out->data[i] = x->data[i] ^ y->data[i];
  }
}

/**
 * Reverse the bits of a 4-bit number.
 *
 * @param byte Input byte.
 * @return byte with lower 4 bits reversed and upper 4 unmodified.
 */
static uint8_t reverse_bits(uint8_t byte) {
  uint8_t out = 0;
  for (size_t i = 0; i < 4; ++i) {
    out <<= 1;
    out |= (byte >> i) & 1;
  }
  return out;
}

/**
 * Reverse the bytes of a 32-bit word.
 *
 * This function is convenient for converting between the processor's native
 * integers, which are little-endian, and NIST's integer representation, which
 * is big-endian.
 *
 * @param word Input word.
 * @return Word with bytes reversed.
 */
static uint32_t reverse_bytes(uint32_t word) {
  uint32_t out = 0;
  for (size_t i = 0; i < sizeof(uint32_t); ++i) {
    out <<= 8;
    out |= (word >> (i << 3)) & 255;
  }
  return out;
}

/**
 * Logical right shift of an AES block.
 *
 * NIST represents AES blocks as big-endian, and a "right shift" in that
 * representation means shifting out the LSB. However, the processor is
 * little-endian, so we need to reverse the bytes before shifting.
 *
 * @param block Input AES block, modified in-place
 * @param nbits Number of bits to shift
 */
static inline void block_shiftr(aes_block_t *block, size_t nbits) {
  // To perform a "right shift" with respect to the big-endian block
  // representation, we traverse the words of the block and, for each word,
  // reverse the bytes, save the new LSB as `carry`, shift right, set the MSB
  // to the last block's carry, and then reverse the bytes back.
  uint32_t carry = 0;
  for (size_t i = 0; i < kAesBlockNumWords; ++i) {
    uint32_t rev = reverse_bytes(block->data[i]);
    uint32_t next_carry = rev & ((1 << nbits) - 1);
    rev >>= nbits;
    rev |= carry << (32 - nbits);
    carry = next_carry;
    block->data[i] = reverse_bytes(rev);
  }
}

/**
 * Retrieve the byte at a given index from the AES block.
 *
 * @param block Input AES block
 * @param index Index of byte to retrieve (must be < `kAesBlockNumBytes`)
 * @return Value of block[index]
 */
static inline uint8_t block_byte_get(const aes_block_t *block, size_t index) {
  return (uint8_t)((char *)block->data)[index];
}

/**
 * Get the number of bytes past the last full block of the buffer.
 *
 * Equivalent to `sz % kAesBlockNumBytes`. Assumes that `kAesBlockNumBytes` is
 * a power of 2.
 *
 * @param sz Number of bytes to represent
 * @return Offset of end of buffer from last full block
 */
static inline size_t get_block_offset(size_t sz) {
  return sz & (kAesBlockNumBytes - 1);
}

/**
 * Get the minimum number of AES blocks needed to represent `sz` bytes.
 *
 * This routine does not run in constant time and should not be used for
 * sensitive input values.
 *
 * @param sz Number of bytes to represent
 * @return Minimum number of blocks needed
 */
static inline size_t get_nblocks(size_t sz) {
  size_t out = sz >> kAesBlockLog2NumBytes;
  if (get_block_offset(sz) != 0) {
    out += 1;
  }
  return out;
}

/**
 * Multiply an element of the GCM Galois field by the polynomial `x`.
 *
 * This corresponds to a shift right in the bit representation, and then
 * reduction with the field modulus.
 *
 * Runs in constant time.
 *
 * @param p Polynomial to be multiplied
 * @param out Buffer for output
 */
static inline void galois_mulx(const aes_block_t *p, aes_block_t *out) {
  // Get the very rightmost bit of the input block (coefficient of x^127).
  uint8_t p127 = block_byte_get(p, kAesBlockNumBytes - 1) & 1;
  // Set the output to p >> 1.
  memcpy(out->data, p->data, kAesBlockNumBytes);
  block_shiftr(out, 1);
  // If the highest coefficient was 1, then subtract the polynomial that
  // corresponds to (modulus - 2^128).
  uint32_t mask = 0 - p127;
  out->data[0] ^= (0xe1 & mask);
}

/**
 * Construct a product table for the hash subkey H.
 *
 * The product table entry at index i is equal to i * H, where both i and H are
 * interpreted as Galois field polynomials.
 *
 * @param H Hash subkey
 * @param product_table Buffer for output
 */
static void make_product_table(const aes_block_t *H,
                               aes_gcm_product_table_t *tbl) {
  // Initialize 0 * H = 0.
  memset(tbl->products[0].data, 0, kAesBlockNumBytes);
  // Initialize 1 * H = H.
  memcpy(tbl->products[0x8].data, H->data, kAesBlockNumBytes);

  // To get remaining entries, we use a variant of "shift and add"; in
  // polynomial terms, a shift is a multiplication by x. Note that, because the
  // processor represents bytes with the MSB on the left and NIST uses a fully
  // little-endian polynomial representation with the MSB on the right, we have
  // to reverse the bits of the indices.
  for (size_t i = 2; i < 16; i += 2) {
    // Find the product corresponding to (i >> 1) * H and multiply by x to
    // shift 1; this will be i * H.
    galois_mulx(&tbl->products[reverse_bits(i >> 1)],
                &tbl->products[reverse_bits(i)]);

    // Add H to i * H to get (i + 1) * H.
    block_xor(&tbl->products[reverse_bits(i)], H,
              &tbl->products[reverse_bits(i + 1)]);
  }
}

/**
 * Computes the "product block" as defined in NIST SP800-38D, section 6.3.
 *
 * The NIST documentation shows a very slow double-and-add algorithm, which
 * iterates through the first operand bit-by-bit. However, since the second
 * operand is always the hash subkey H, we can speed things up significantly
 * with a little precomputation.
 *
 * The `H_table` input should be a precomputed table with the products of H and
 * 256 all possible byte values (see `make_product_table`).
 *
 * This operation corresponds to multiplication in the Galois field with order
 * 2^128, modulo the polynomial x^128 +  x^8 + x^2 + x + 1
 *
 * @param p Polynomial to multiply
 * @param H_table Precomputed product table for the hash subkey
 * @param result Block in which to store output
 */
static void galois_mul(const aes_block_t *p, const aes_gcm_product_table_t *tbl,
                       aes_block_t *result) {
  // Initialize the result to 0.
  memset(result->data, 0, kAesBlockNumBytes);

  // 4-bit windows, so number of windows is 2x number of bytes.
  const size_t kNumWindows = kAesBlockNumBytes << 1;

  // To compute the product, we iterate through the bytes of the input block,
  // considering the most significant (in polynomial terms) first. For each
  // byte b, we:
  //   * multiply `result` by x^8 (shift all coefficients to the right)
  //   * reduce the shifted `result` modulo the field modulus
  //   * look up the product `b * H` and add it to `result`
  //
  // We can skip the shift and reduce steps on the first iteration, since
  // `result` is 0.
  for (size_t i = 0; i < kNumWindows; ++i) {
    if (i != 0) {
      // Save the most significant half-byte of `result` before shifting.
      uint8_t overflow = block_byte_get(result, kAesBlockNumBytes - 1) & 0x0f;
      // Shift `result` to the right, discarding high bits.
      block_shiftr(result, 4);
      // Look up the product of `overflow` and the low terms of the modulus in
      // the precomputed table.
      uint16_t reduce_term = kGFReduceTable[overflow];
      // Add (xor) this product to the low bits to complete modular reduction.
      // This works because (low + x^128 * high) is equivalent to (low + (x^128
      // - modulus) * high).
      result->data[0] ^= reduce_term;
    }

    // Add the product of the next window and H to `result`. We process the
    // windows starting with the most significant polynomial terms, which means
    // starting from the last byte and proceeding to the first.
    uint8_t pi = block_byte_get(p, (kNumWindows - 1 - i) >> 1);

    // Select the less significant 4 bits if i is even, or the more significant
    // 4 bits if i is odd. This does not need to be constant time, since the
    // values of i in this loop are constant.
    if ((i & 1) == 1) {
      pi >>= 4;
    } else {
      pi &= 0x0f;
    }
    block_xor(result, &tbl->products[pi], result);
  }
}

/**
 * Advances the GHASH state for the given input.
 *
 * This function is convenient for computing the GHASH of large, concatenated
 * buffers. Given a state representing GHASH(A) and a new input B, this
 * function will return a state representing GHASH(A || B || <padding for B>).
 *
 * Pads the input with 0s on the right-hand side if needed so that the input
 * size is a multiple of the block size.
 *
 * The product table should match the format from `make_product_table`.
 *
 * @param H_table Precomputed product table
 * @param input_len Length of input in bytes
 * @param input Input buffer
 * @param state GHASH state, updated in place
 */
static void aes_gcm_ghash_update(const aes_gcm_product_table_t *tbl,
                                 const size_t input_len, const uint8_t *input,
                                 aes_block_t *state) {
  // Calculate the number of AES blocks needed for the input.
  size_t nblocks = get_nblocks(input_len);

  // Main loop.
  for (size_t i = 0; i < nblocks; ++i) {
    // Construct block i of the input.
    aes_block_t input_block;
    if ((i == nblocks - 1) && (get_block_offset(input_len) != 0)) {
      // Last block is not full; pad with zeroes.
      size_t nbytes = get_block_offset(input_len);
      memset(input_block.data, 0, kAesBlockNumBytes);
      memcpy(input_block.data, input, nbytes);
    } else {
      // Full block; copy data and advance input pointer.
      memcpy(input_block.data, input, kAesBlockNumBytes);
      input += kAesBlockNumBytes;
    }
    // XOR `state` with the next input block.
    block_xor(state, &input_block, state);
    // Multiply state by H and update.
    aes_block_t yH;
    galois_mul(state, tbl, &yH);
    memcpy(state->data, yH.data, kAesBlockNumBytes);
  }
}

aes_error_t aes_gcm_ghash(const aes_block_t *hash_subkey,
                          const size_t input_len, const uint8_t *input,
                          aes_block_t *output) {
  // Compute the product table for H.
  aes_gcm_product_table_t tbl;
  make_product_table(hash_subkey, &tbl);

  // If the input length is not a multiple of the block size, fail.
  if (get_block_offset(input_len) != 0) {
    return kAesInternalError;
  }

  // Initialize the GHASH state to 0.
  memset(output->data, 0, kAesBlockNumBytes);

  // Update the GHASH state with the input.
  aes_gcm_ghash_update(&tbl, input_len, input, output);

  return kAesOk;
}
