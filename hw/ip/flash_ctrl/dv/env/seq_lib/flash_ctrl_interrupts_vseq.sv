// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: Remove later
//  name: interrupts
//  desc: '''
//        Perform accesses in order to raise all interrupts given in register map.
//        Check behaviour of Interrupt Enable and Status Registers.
//        '''
//  milestone: V2
//  tests: [flash_ctrl_interrupts]

// flash_ctrl_interrupts Test

// Pseudo Code  TODO
// Initialise (All)
// Loop { 32 .. 64 }
// TODO

class flash_ctrl_interrupts_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_interrupts_vseq)

  `uvm_object_new

  // Class Members
  bit             poll_fifo_status = 1;
  rand flash_op_t flash_op;
  rand data_q_t   flash_op_data;
  rand uint       bank;

  bit [NUM_FLASH_INTERRUPTS-1:0] csr_intr_enable;
  bit [NUM_FLASH_INTERRUPTS-1:0] csr_intr_state;
  
  // Test Iteration Limits (Max, Min)
  localparam uint OUTER_MIN = 8;   // Schemes
  localparam uint OUTER_MAX = 16;
  localparam uint INNER_MIN = 32;  // Flash Ops
  localparam uint INNER_MAX = 64;

  // Read Fifo Levels
  localparam uint RdLvlMin = 4;
  localparam uint RdLvlMax = flash_ctrl_env_pkg::ReadFifoDepth;

  // Constraint for Bank.
  constraint bank_c {
    bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
  }

  // Constraint for controller address to be in the relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1)]};
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  // Constraint for the Flash Operation
  constraint flash_op_c {
    // Bank Erase is only supported for Data & 1st Info Partitions
    flash_op.partition != FlashPartData && flash_op.partition != FlashPartInfo ->
        flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;

    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      flash_op.partition == FlashPartInfo ->
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      flash_op.partition == FlashPartInfo1 ->
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (flash_op.partition == FlashPartInfo2) {
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram,
                        flash_ctrl_pkg::FlashOpErase};

    flash_op.erase_type dist {
      flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
  //flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];  // TODO: Potential Issue
    flash_op.num_words < cfg.seq_cfg.op_max_words - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  // Flash ctrl operation data queue - used for programing or reading the flash.
  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    if (flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram}) {
      flash_op_data.size() == flash_op.num_words;
    } else {
      flash_op_data.size() == 0;
    }
  }

  // Bit vector representing which of the mp region cfg CSRs to enable.
  rand bit [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

  // Memory Protection Regions
  constraint en_mp_regions_c {$countones(en_mp_regions) == cfg.seq_cfg.num_en_mp_regions;}

  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {
    solve en_mp_regions before mp_regions;

    foreach (mp_regions[i]) {
      mp_regions[i].en          == mubi4_bool_to_mubi(en_mp_regions[i]);
      mp_regions[i].read_en     == MuBi4True;
      mp_regions[i].program_en  == MuBi4True;
      mp_regions[i].erase_en    == MuBi4True;
      mp_regions[i].scramble_en == MuBi4False;
      mp_regions[i].ecc_en      == MuBi4False;
      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
      };

      mp_regions[i].start_page inside {[0 : FlashNumPages - 1]};
      mp_regions[i].num_pages inside {[1 : FlashNumPages - mp_regions[i].start_page]};
      mp_regions[i].num_pages <= cfg.seq_cfg.mp_region_max_pages;

      // If overlap is not allowed, then each configured region is uniquified.
      // This creates an ascending order of mp_regions that are configured, so we shuffle it in
      // post_randomize.
      if (!cfg.seq_cfg.allow_mp_region_overlap) {
        foreach (mp_regions[j]) {
          if (i != j) {
            !mp_regions[i].start_page inside {
              [mp_regions[j].start_page:mp_regions[j].start_page + mp_regions[j].num_pages]
            };
          }
        }
      }
    }
  }

  // Information partitions memory protection settings.
  rand flash_bank_mp_info_page_cfg_t
         mp_info_pages[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint mp_info_pages_c {

    foreach (mp_info_pages[i, j]) {
      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];
      foreach (mp_info_pages[i][j][k]) {
        mp_info_pages[i][j][k].en          == MuBi4True;
        mp_info_pages[i][j][k].read_en     == MuBi4True;
        mp_info_pages[i][j][k].program_en  == MuBi4True;
        mp_info_pages[i][j][k].erase_en    == MuBi4True;
        mp_info_pages[i][j][k].scramble_en == MuBi4False;
        mp_info_pages[i][j][k].ecc_en      == MuBi4False;
        mp_info_pages[i][j][k].he_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  mubi4_t default_region_read_en;
  mubi4_t default_region_program_en;
  mubi4_t default_region_erase_en;
  mubi4_t default_region_scramble_en;
  rand mubi4_t default_region_he_en;
  rand mubi4_t default_region_ecc_en;

  // Bank Erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint bank_erase_en_c {
    foreach (bank_erase_en[i]) {
      bank_erase_en[i] == 1;
    }
  }

  // High Endurance
  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  constraint default_region_ecc_en_c {default_region_ecc_en == MuBi4False;}

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op.
    cfg.seq_cfg.op_max_words = 32;  // TODO
 
    // Enable NO memory protection regions
    cfg.seq_cfg.num_en_mp_regions = 0;

    // Enable High Endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    // Enable Read Only on Info Partitions
    cfg.seq_cfg.op_readonly_on_info_partition  = 0;
    cfg.seq_cfg.op_readonly_on_info1_partition = 0;

  endfunction : configure_vseq

  // ----------
  // -- Body --
  // ----------
  
  virtual task body();
        
    `uvm_info(`gfn, "INTERRUPT TESTS", UVM_LOW)

    init_flash_regions();
    display_mp_region_info();

//  fork
//    test_interrupt_test_reg(); 
//    interrupt_checker(csr_intr_test);
//  join_any
//  disable fork;

//  test_op_done_intr();   

    test_fifo_rd_interrupts();      
  
//  test_fifo_prog_interrupts();

  endtask : body

  // ------------------------------
  // -- Task: init_flash_regions --
  // ------------------------------

  // Task to initialize the Flash Access (Enable All Regions)
  virtual task init_flash_regions();

    // Default Region Settings
    default_region_read_en     = MuBi4True;
    default_region_program_en  = MuBi4True;
    default_region_erase_en    = MuBi4True;
    default_region_scramble_en = MuBi4False;

    // Enable Bank Erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // Initialize MP Regions
    foreach (mp_regions[k]) begin
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_MEDIUM)
    end

    // Initialize Default Regions
    flash_ctrl_default_region_cfg(
      .read_en(default_region_read_en), .program_en(default_region_program_en),
      .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
      .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    // Initialize Info MP Regions
    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO Region [%0d, %0d, %0d] : %p", i, j, k,
        mp_info_pages[i][j][k]), UVM_MEDIUM)
    end

  endtask : init_flash_regions

  // ----------------------------
  // -- Task: display_intr_reg --
  // ----------------------------

  virtual task display_intr_reg(input string reg_name, input bit [NUM_FLASH_INTERRUPTS-1:0] reg_val);
    string reg_str = "";
    foreach (reg_val[i]) begin
      unique case (i)    
        5: reg_str = {reg_str, $sformatf("prog_empty:%0b ", reg_val[5])};
        4: reg_str = {reg_str, $sformatf("prog_lvl:%0b, ",  reg_val[4])};
        3: reg_str = {reg_str, $sformatf("rd_full:%0b, ",   reg_val[3])};
        2: reg_str = {reg_str, $sformatf("rd_lvl:%0b, ",    reg_val[2])};
        1: reg_str = {reg_str, $sformatf("op_done:%0b, ",   reg_val[1])};
        0: reg_str = {reg_str, $sformatf("corr_err:%0b",    reg_val[0])};
        default : `uvm_fatal(`gfn, "No Match seen for Register Bit, FAIL")
      endcase   
    end  
    `uvm_info(`gfn, $sformatf("Interrupt Register : %s : 'b%06b : %s", reg_name, reg_val, reg_str), UVM_LOW);  
  endtask : display_intr_reg

  // ------------------------------------
  // -- Task : test_interrupt_test_reg --
  // ------------------------------------

  virtual task test_interrupt_test_reg();
  
    // Local Variables
    string            bit_name;
    flash_ctrl_intr_e bit_e;
    uint              num_iter;
  
    // --------------------------------------------------------
    // -- Test : Interrupt Test Register Feature (INTR_TEST) --
    // --------------------------------------------------------

    `uvm_info(`gfn, "Test : Interrupt Test Register Feature", UVM_LOW)

    // Note: Register INTR_ENABLE Controls the IRQ Output, Not the Internal Status Flag

    // Note: variable 'csr_intr_test' (Write Only Register) is defined in the Base Class, 
    //       and passed to the  interrupt checker by reference

    // Ensure INTR_TEST is Inactive, (Reset Condition)
    csr_wr(.ptr(ral.intr_test), .value('0));

    // Iterate
    num_iter = $urandom_range(INNER_MIN, INNER_MAX);
    for (int i = 0; i < num_iter; i++) begin

      `uvm_info(`gfn, $sformatf("Iteration : %0d : %0d", i+1, num_iter), UVM_LOW)

      // Randomly Enable Interrupts and the Interrupt Test Option
      csr_intr_enable = $urandom_range(0, (2**NUM_FLASH_INTERRUPTS)-1);
      csr_intr_test   = $urandom_range(0, (2**NUM_FLASH_INTERRUPTS)-1);

      // Write to Registers    
      csr_wr(.ptr(ral.intr_enable), .value(csr_intr_enable));
      csr_wr(.ptr(ral.intr_test),   .value(csr_intr_test));

      // Compare Interrupt State with the Expected Status Response      
      csr_rd(.ptr(ral.intr_state), .value(csr_intr_state));

      // Display Info
      display_intr_reg("FLASH_CTRL.INTR_ENABLE", csr_intr_enable);
      display_intr_reg("FLASH_CTRL.INTR_TEST  ", csr_intr_test);
      display_intr_reg("FLASH_CTRL.INTR_STATE ", csr_intr_state);

      // Check Expected Functionality.  Note that INTR_ENABLE has no effect on the Status Register.        
      foreach (csr_intr_state[i]) begin      
        bit_e = flash_ctrl_intr_e'(i);
        bit_name = bit_e.name();            
        if (((csr_intr_test[i]==0) && (csr_intr_state[i]==0)) || 
            ((csr_intr_test[i]==1) && (csr_intr_state[i]==1))) 
          `uvm_info(`gfn, $sformatf("Interrupt Status Register Bit[%0d] (%s) : PASS", i, bit_name), UVM_HIGH)
        else
          `uvm_error(`gfn, $sformatf("Interrupt Status Register Bit[%0d] (%s) : FAIL", i, bit_name))
      end      
      // Clear Interrupt Status Register
      csr_wr(.ptr(ral.intr_state), .value('1));
    end

    // Restore Reset Values    
    csr_intr_test = '0;
    csr_wr(.ptr(ral.intr_enable), .value('0));
    csr_wr(.ptr(ral.intr_test),   .value(csr_intr_test));

  endtask : test_interrupt_test_reg

  // -----------------------------
  // -- Task: interrupt Checker --
  // -----------------------------

  // Simple Model For Interrupt Checks, used with test1
  virtual task interrupt_checker(ref bit [NUM_FLASH_INTERRUPTS-1:0] intr_test);

    // Local Variables
    bit [NUM_FLASH_INTERRUPTS-1:0] csr_intr_enable;
    bit [NUM_FLASH_INTERRUPTS-1:0] csr_intr_state;
    string bit_name;
    flash_ctrl_intr_e bit_e;

    forever begin                                                                                                                      
                                                                                                                                       
      // Trigger On a Change at the Interrupt Pins                                                                                     
      fork      
        @(cfg.flash_ctrl_intr_vif.pins[NUM_FLASH_INTERRUPTS-1:0]);                                                                       
        wait_intr_timeout(10ms, "DUT Interrupt Pins");
      join_any
      disable fork;                                                                                                                               
      `uvm_info(`gfn, $sformatf("(checker) Hardware Interrupt Pins : 'b%06b", cfg.flash_ctrl_intr_vif.pins[NUM_FLASH_INTERRUPTS-1:0]), UVM_LOW)  
                                                                                                                                       
      // Read Interrupt Registers Via the Backdoor                                                                                     
 
      // Get Register Values via the Backdoor                                                                                          
      csr_rd(.ptr(ral.intr_enable), .value(csr_intr_enable), .backdoor(1));                                                            
      csr_rd(.ptr(ral.intr_state),  .value(csr_intr_state),  .backdoor(1));                                                            
                                                                                                                                       
      // Model and Check Behaviour                                                                                                     
      foreach (csr_intr_state[i]) begin                                                                                                
        bit_e    = flash_ctrl_intr_e'(i);                                                                                              
        bit_name = bit_e.name();                                                                                                       
        if (cfg.flash_ctrl_intr_vif.pins[i] == 1) begin                                                                                
          if (((csr_intr_test[i]==0) && (csr_intr_state[i]== 1)) || ((csr_intr_test[i]==1) && (csr_intr_state[i]==0)))            
            `uvm_error(`gfn, $sformatf("(checker) Interrupt Not Seen but Expected, Bit[%0d] (%s), FAIL", i, bit_name))                           
          else if (((csr_intr_test[i]==0) && (csr_intr_state[i]== 0)) || ((csr_intr_test[i]==1) && (csr_intr_state[i]==1)))            
            `uvm_info(`gfn, $sformatf("(checker) Interrupt Seen and Expected, Bit[%0d] (%s), PASS", i, bit_name), UVM_LOW)                       
          else                                                                                                                         
            `uvm_fatal(`gfn, "(checker) Illegal Interrupt Condition, FAIL")                                                                      
        end                                                                                                                            
      end                                                                                                                              

    end                                                                                                                                
      
  endtask : interrupt_checker

  // ------------------------------
  // -- Task : test_op_done_intr --
  // ------------------------------

  virtual task test_op_done_intr();

    // Local Variables
    uvm_reg_data_t data;
    uint           num_iter;

    // ---------------------------------------------------------------------------------------
    // -- Test : Flash Erase, Program and Read using 'op_done' Interrupt instead of Polling --
    // ---------------------------------------------------------------------------------------

    `uvm_info(`gfn, "Test : Flash Erase, Program and Read using 'op_done' Interrupt instead of Polling", UVM_LOW)
  
    // Enable INTR : op_done          
    data = get_csr_val_with_updated_field(ral.intr_enable.op_done, data, 1);  
    csr_wr(.ptr(ral.intr_enable), .value(data));
                    
    // Iterate
    num_iter = $urandom_range(INNER_MIN, INNER_MAX);
    for (int i = 0; i < num_iter; i++) begin
  
      `uvm_info(`gfn, $sformatf("Iteration : %0d : %0d", i+1, num_iter), UVM_LOW)

      // Randomize the Members of the Class
      `DV_CHECK_RANDOMIZE_FATAL(this)
                                    
      `uvm_info(`gfn, $sformatf("Flash Op : %p", flash_op), UVM_LOW)

      // If the 'Info' Partition is Selected, Turn On the HW Access Signals
      // to allow SW access to Creator, Owner and Isolation Partitions
      en_sw_rw_part_info(flash_op, lc_ctrl_pkg::On);

      // Initialise Flash Content
      init_flash_content(flash_op);

      // Start Controller Read, Program or Erase
      unique case (flash_op.op)

        FlashOpRead :
        begin
          flash_op_data.delete();
          flash_ctrl_start_op(flash_op);
          wait_flash_op_done();
          flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
          `uvm_info(`gfn, $sformatf("Read Data : %0p", flash_op_data), UVM_LOW)
          cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
        end

        FlashOpProgram :
        begin
          data_q_t exp_data;
          exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
          flash_ctrl_start_op(flash_op);
          flash_ctrl_write(flash_op_data, poll_fifo_status);
          wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
          `uvm_info(`gfn, $sformatf("Program Data : %0p", flash_op_data), UVM_LOW)
          cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
        end

        FlashOpErase :
        begin
          data_q_t exp_data;
          exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);        
          flash_ctrl_start_op(flash_op);        
          wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));        
          `uvm_info(`gfn, "Erase Data", UVM_LOW)
          cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);      
        end

        default : `uvm_fatal(`gfn, "Flash Operation Unrecognised, FAIL")

      endcase

      // If the 'Info' Partition is Selected, Turn Off the HW Access Signals
      // to disallow SW access to Creator, Owner and Isolation Partitions
      en_sw_rw_part_info (flash_op, lc_ctrl_pkg::Off);

    end

  endtask : test_op_done_intr

  // ------------------------------------
  // -- Task : test_fifo_rd_interrupts --
  // ------------------------------------

  virtual task test_fifo_rd_interrupts();

    // NOTE : Constraints
    // 1) Data Partiions Only
    // 2) FIFO LVL Restriction 4 - 16 words
    // 3) num_words Restriction 8 - 64 words

    // Local Variables
    uint           fifo_max_rd_depth = flash_ctrl_env_pkg::ReadFifoDepth;
    uint           idx;
    uvm_reg_data_t data;
    uint           curr_fifo_lvl;
    uint           num_words_rem;
    uint           rd_lvl;
    bit            done;
    bit            rd_intr_opt;
    uint           num_outer;
    uint           num_inner;

    // -----------------------------------
    // -- Test : Verify READ Interrupts --
    // -----------------------------------

    `uvm_info(`gfn, "Test : Verify READ Interrupts", UVM_LOW)

    // OUTER LOOP

    num_outer = $urandom_range(OUTER_MIN, OUTER_MAX);
    for (int i = 0; i < num_outer; i++) begin

      // Decide if test will use the 'rd_full' or the 'rd_lvl' Interrupt
      randcase
        1 : rd_intr_opt = 0;  // 'rd_full'
        2 : rd_intr_opt = 1;  // 'rd_lvl'
      endcase

      // Enable Desired Interrupts
      `uvm_info("DEBUG", "--> Clearing intr_enable", UVM_LOW)
      csr_wr(.ptr(ral.intr_enable), .value(0));
      if (rd_intr_opt == 0) begin
        `uvm_info(`gfn, "Test Chose : Use 'rd_full' Interrupt", UVM_LOW)
        
        data =        get_csr_val_with_updated_field(ral.intr_enable.rd_full, data, 1);  // rd_full
        data = data | get_csr_val_with_updated_field(ral.intr_enable.rd_lvl, data,  0);  // rd_lvl
      
      end else begin
        `uvm_info(`gfn, "Test Chose : Use 'rd_lvl' Interrupt", UVM_LOW)
        rd_lvl = $urandom_range(RdLvlMin, RdLvlMax);
        `uvm_info(`gfn, $sformatf("Test Chose : Read Level : %0d", rd_lvl), UVM_LOW)
        csr_wr(.ptr(ral.fifo_lvl.rd), .value(rd_lvl));
        csr_rd_check(.ptr(ral.fifo_lvl.rd), .compare_value(rd_lvl));
        
        data =        get_csr_val_with_updated_field(ral.intr_enable.rd_lvl, data,  1);  // rd_lvl
        data = data | get_csr_val_with_updated_field(ral.intr_enable.rd_full, data, 0);  // rd_full
      
      end
      data = data | get_csr_val_with_updated_field(ral.intr_enable.op_done, data, 1);  // op_done

      `uvm_info("DEBUG", $sformatf("--> Writing intr_enable : %b", data), UVM_LOW)

      csr_wr(.ptr(ral.intr_enable), .value(data));

      // INNER LOOP

      num_inner = $urandom_range(INNER_MIN, INNER_MAX);
      for (int j = 0; j < num_inner; j++) begin

        `uvm_info(`gfn, $sformatf("Iteration : %0d.%0d / %0d.%0d", i+1, j+1,
                          num_outer, num_inner), UVM_LOW)

        // Randomize the Members of the Class (Using Flash Read) -- TODO : Just Data Partition ATM
        `DV_CHECK_RANDOMIZE_WITH_FATAL(this, flash_op.op        == FlashOpRead;
                                             flash_op.partition == FlashPartData;
                                             flash_op.addr      == 0;)

        // Select a Number of Words to Read - TODO
        flash_op.num_words = $urandom_range(8, 64);
        num_words_rem = flash_op.num_words;

        `uvm_info(`gfn, $sformatf("Flash Op : %0p", flash_op), UVM_LOW)

        // If the 'Info' Partition is Selected, Turn On the HW Access Signals
        en_sw_rw_part_info(flash_op, lc_ctrl_pkg::On);

        // Initialise Flash Content
        init_flash_content(flash_op);

        // Initialize
        flash_op_data.delete();
        idx = 0;

        // Start Op
        flash_ctrl_start_op(flash_op);
        done = 0;
        while (done == 0)
        begin
          `uvm_info(`gfn, "Waiting For 'rd_full', 'rd_lvl' or 'op_done' Interrupt", UVM_LOW)
          fork
            @(posedge cfg.flash_ctrl_intr_vif.pins[FlashCtrlIntrOpDone]);
            begin
              if (rd_intr_opt == 0)
                @(posedge cfg.flash_ctrl_intr_vif.pins[FlashCtrlIntrRdFull]);
              else
                @(posedge cfg.flash_ctrl_intr_vif.pins[FlashCtrlIntrRdLvl]);
            end
            wait_intr_timeout(1ms, "Interrupts : 'op_done', 'rd_full', rd'_lvl'");
          join_any
          disable fork;

          // Process Interrupt
          if (cfg.flash_ctrl_intr_vif.pins[FlashCtrlIntrRdLvl]) begin  // Interrupt 'rd_lvl'
            process_rd_intr(.intr_str("rd_lvl"), .reg_ptr(ral.intr_state.rd_lvl),
                            .num_words_rem(num_words_rem), .pred_rd_lvl(rd_lvl),
                            .idx(idx));
          end else begin
            if (cfg.flash_ctrl_intr_vif.pins[FlashCtrlIntrRdFull]) begin  // Interrupt 'rd_full'
              process_rd_intr(.intr_str("rd_full"), .reg_ptr(ral.intr_state.rd_full),
                              .num_words_rem(num_words_rem), .pred_rd_lvl(fifo_max_rd_depth),
                              .idx(idx));
            end else begin
              if (cfg.flash_ctrl_intr_vif.pins[FlashCtrlIntrOpDone]) begin  // Interrupt 'op_done'
                process_rd_intr(.intr_str("op_done"), .reg_ptr(ral.intr_state.op_done),
                                .num_words_rem(num_words_rem), .pred_rd_lvl(num_words_rem),
                                .idx(idx));
                done = 1;  // Complete Read Operation
              end else begin
                `uvm_fatal(`gfn, "Interrupt Error Occurred - FAIL")
              end
            end
          end

        end

        `uvm_info(`gfn, "CHECK DATA INTEGRITY", UVM_LOW)
        cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);  // Check Data Integrity

        // If the 'Info' Partition is Selected, Turn Off the HW Access Signals
        en_sw_rw_part_info (flash_op, lc_ctrl_pkg::Off);
  
        #1us;  // TODO REMOVE

      end

    end

  endtask : test_fifo_rd_interrupts
 
  // ------------------------------
  // -- Task : wait_intr_timeout --
  // ------------------------------
  
  virtual task wait_intr_timeout(input time timeout, input string msg);
    
    fork
      forever begin
        #(timeout/100);
        `uvm_info(`gfn, "Timeout Tick ...", UVM_LOW)          
      end
      begin
        #(timeout);
        `uvm_fatal(`gfn, $sformatf("Timed Out Waiting for Interrupt : %s, FAIL", msg))             
      end
    join_any
    disable fork;
    
  endtask : wait_intr_timeout

  // -----------------------------------
  // -- Task : display_mp_region_info --
  // -----------------------------------

  virtual function void display_mp_region_info();
    string en_msg;
    `uvm_info(`gfn, "MP REGION INFORMATION (DATA PARTITIONS)", UVM_MEDIUM)
    foreach (mp_regions[i]) begin
      en_msg = (mp_regions[i].en == MuBi4True) ? "Enabled": "Disabled";
      `uvm_info(`gfn,
        $sformatf("MPR%0d : From : 0x%03x, To : 0x%03x : From : 0x%08x, To : 0x%08x, %s", i,
          mp_regions[i].start_page, mp_regions[i].start_page+mp_regions[i].num_pages,
            mp_regions[i].start_page*(FullPageNumWords*4),
              (mp_regions[i].start_page+mp_regions[i].num_pages)*(FullPageNumWords*4),
                en_msg), UVM_MEDIUM)
    end
  endfunction :  display_mp_region_info

  // ---------------------------
  // -- Task : read_fifo_data --
  // ---------------------------
  
  virtual task read_fifo_data(input uint num_words, ref uint idx);
    uvm_reg_data_t data;
    for (int i = 0; i < num_words; i++) begin
      mem_rd(.ptr(ral.rd_fifo), .offset(0), .data(data));
      flash_op_data.push_back(data);      
      `uvm_info(`gfn, $sformatf("Word[%0d] : Read FIFO : 0x%0x", idx++, data), UVM_LOW) 
    end
  endtask : read_fifo_data

  // ---------------------------
  // -- Task : prog_fifo_data --
  // ---------------------------

  virtual task prog_fifo_data(input uint num_words, input data_q_t data, ref uint idx);        
    for (int i = 0; i < num_words; i++) begin
      mem_wr(.ptr(ral.prog_fifo), .offset(0), .data(data[i]));
      `uvm_info(`gfn, $sformatf("Word[%0d] : Program FIFO : 0x%0x", idx++, data[i]), UVM_LOW) 
    end 
  endtask : prog_fifo_data

  // ----------------------------
  // -- Task : process_rd_intr --
  // ----------------------------

  virtual task process_rd_intr(input string intr_str, input uvm_object reg_ptr, 
                               ref uint num_words_rem, input uint pred_rd_lvl, ref uint idx);

    // Local Variable
    uint curr_fifo_lvl;

    `uvm_info(`gfn, $sformatf("Seen Interrupt : %s", intr_str), UVM_LOW)                                                                                                                                                                                        
    `uvm_info(`gfn, $sformatf("Check Status : %s", intr_str), UVM_LOW)                                                        
    csr_rd_check(.ptr(reg_ptr), .compare_value(1));                                                      

    // Predict Status
    ral.curr_fifo_lvl.rd.predict(pred_rd_lvl);                                                                             

`uvm_info("DEBUG", $sformatf("--> Predicted Rd Level : %0d", pred_rd_lvl), UVM_LOW)

    if (intr_str inside {"rd_lvl", "rd_full"})  // Track Remaining Words
      num_words_rem -= pred_rd_lvl;                                      

    csr_rd(.ptr(ral.curr_fifo_lvl.rd), .value(curr_fifo_lvl)); 

`uvm_info("DEBUG", $sformatf("--> Curr Fifo Level : %0d", curr_fifo_lvl), UVM_LOW)    
                                                              
    read_fifo_data(curr_fifo_lvl, idx);  // Read Data from FIFO                                                          

    `uvm_info(`gfn, $sformatf("Clear Status : %s", intr_str), UVM_LOW)                
    csr_wr(.ptr(reg_ptr), .value(1));                               

  endtask : process_rd_intr

  // -------------------------------
  // -- Task : init_flash_content --
  // -------------------------------

  // Initialize Flash Content
  virtual task init_flash_content(ref flash_op_t flash_op);
    cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
    if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
      cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
    end else begin
      cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
    end
 endtask : init_flash_content

endclass : flash_ctrl_interrupts_vseq
