`timescale 1ns / 1ps

//=============================================================================
// FPU Extreme Values Debug Testbench
// Purpose: Trace and debug timeout issues with FP80_LARGE and FP80_TINY
//=============================================================================

module fpu_extreme_debug_tb();

    //=========================================================================
    // Clock and Reset
    //=========================================================================
    reg clk;
    reg reset;

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end

    //=========================================================================
    // FPU Interface Signals
    //=========================================================================

    // Instruction interface
    reg [7:0]   instruction;
    reg [2:0]   stack_index;
    reg         execute;
    wire        ready;
    wire        error;

    // Data interface
    reg [79:0]  data_in;
    wire [79:0] data_out;
    reg [31:0]  int_data_in;
    wire [31:0] int_data_out;

    // Memory operand format
    reg         has_memory_op;
    reg [1:0]   operand_size;
    reg         is_integer;
    reg         is_bcd;

    // Control/Status
    reg [15:0]  control_in;
    reg         control_write;
    wire [15:0] status_out;
    wire [15:0] control_out;
    wire [15:0] tag_word_out;
    wire        int_request;

    //=========================================================================
    // Test Constants
    //=========================================================================

    // FP80 values
    localparam FP80_ZERO        = 80'h0000_0000000000000000;
    localparam FP80_ONE         = 80'h3FFF_8000000000000000;
    localparam FP80_TWO         = 80'h4000_8000000000000000;

    // Extreme values
    localparam FP80_LARGE       = 80'h7FFE_FFFFFFFFFFFFFFFF;  // Largest finite positive
    localparam FP80_TINY        = 80'h0001_8000000000000000;  // Smallest positive normal

    // Instructions (from FPU_Core.v)
    localparam INST_FADD        = 8'h10;
    localparam INST_FMUL        = 8'h14;
    localparam INST_FDIV        = 8'h16;
    localparam INST_FLD         = 8'h20;  // Push from memory/ST(i)
    localparam INST_FINIT       = 8'hF0;

    //=========================================================================
    // FPU Instance
    //=========================================================================

    FPU_Core fpu (
        .clk(clk),
        .reset(reset),

        // Instruction interface
        .instruction(instruction),
        .stack_index(stack_index),
        .execute(execute),
        .ready(ready),
        .error(error),

        // Data interface
        .data_in(data_in),
        .data_out(data_out),
        .int_data_in(int_data_in),
        .int_data_out(int_data_out),

        // Memory operand format
        .has_memory_op(has_memory_op),
        .operand_size(operand_size),
        .is_integer(is_integer),
        .is_bcd(is_bcd),

        // Control/Status
        .control_in(control_in),
        .control_write(control_write),
        .status_out(status_out),
        .control_out(control_out),
        .tag_word_out(tag_word_out),
        .int_request(int_request)
    );

    //=========================================================================
    // Debug Monitoring
    //=========================================================================

    reg [31:0] cycle_count;

    always @(posedge clk) begin
        if (reset)
            cycle_count <= 0;
        else
            cycle_count <= cycle_count + 1;
    end

    //=========================================================================
    // Tasks
    //=========================================================================

    task init_fpu();
        begin
            @(posedge clk);
            instruction <= INST_FINIT;
            stack_index <= 3'd0;
            data_in <= FP80_ZERO;
            has_memory_op <= 1'b0;
            operand_size <= 2'd3;
            is_integer <= 1'b0;
            is_bcd <= 1'b0;
            execute <= 1'b1;

            @(posedge clk);
            execute <= 1'b0;

            // Wait for ready to go low then high
            wait(!ready);
            wait(ready);
            @(posedge clk);
            $display("[%0t] FPU initialized", $time);
        end
    endtask

    task push_value(input [79:0] value);
        begin
            @(posedge clk);
            instruction <= INST_FLD;
            stack_index <= 3'd0;
            data_in <= value;
            has_memory_op <= 1'b1;
            operand_size <= 2'd3;  // tbyte
            is_integer <= 1'b0;
            is_bcd <= 1'b0;
            execute <= 1'b1;

            @(posedge clk);
            execute <= 1'b0;

            // Wait for ready to go low then high
            wait(!ready);
            wait(ready);
            @(posedge clk);
        end
    endtask

    task execute_and_trace(input [7:0] inst, input [2:0] idx, input string name, input integer timeout_cycles);
        integer cycles;
        begin
            @(posedge clk);

            instruction <= inst;
            stack_index <= idx;
            data_in <= FP80_ZERO;
            has_memory_op <= 1'b0;
            operand_size <= 2'd3;
            is_integer <= 1'b0;
            is_bcd <= 1'b0;
            execute <= 1'b1;

            $display("\n[%0t] Starting %s operation (inst=0x%h)", $time, name, inst);

            @(posedge clk);
            execute <= 1'b0;

            // Wait for ready to go low (FPU starts processing)
            cycles = 0;
            while (ready && cycles < 100) begin
                @(posedge clk);
                cycles = cycles + 1;
            end

            if (cycles >= 100) begin
                $display("[%0t] WARNING: ready never went low", $time);
            end

            // Wait for completion with timeout
            cycles = 0;
            while (!ready && cycles < timeout_cycles) begin
                @(posedge clk);
                cycles = cycles + 1;

                // Print progress every 1000 cycles
                if (cycles % 1000 == 0) begin
                    $display("[%0t] %s: %0d cycles elapsed, still busy", $time, name, cycles);
                    $display("  FPU state=%0d, arith_enable=%b, arith_done=%b",
                        fpu.state, fpu.arith_enable, fpu.arith_done);
                end

                // Print more detail at 100 cycle intervals early on
                if (cycles > 0 && cycles <= 500 && cycles % 100 == 0) begin
                    $display("[%0t] %s: %0d cycles, state=%0d, arith_en=%b, arith_done=%b, arith_op=%0d",
                        $time, name, cycles, fpu.state, fpu.arith_enable, fpu.arith_done, fpu.arith_operation);
                end
            end

            if (cycles >= timeout_cycles) begin
                $display("[%0t] TIMEOUT: %s after %0d cycles", $time, name, cycles);
                $display("  FPU state=%0d", fpu.state);
                $display("  arith_enable=%b, arith_done=%b, arith_operation=%0d",
                    fpu.arith_enable, fpu.arith_done, fpu.arith_operation);
                $display("  Status word: %04h", status_out);
            end else begin
                $display("[%0t] %s completed in %0d cycles", $time, name, cycles);
                $display("  Status word: %04h", status_out);
            end

            @(posedge clk);
        end
    endtask

    //=========================================================================
    // Main Test
    //=========================================================================

    initial begin
        $dumpfile("fpu_extreme_debug_tb.vcd");
        $dumpvars(0, fpu_extreme_debug_tb);

        $display("================================================================");
        $display("FPU Extreme Values Debug Testbench");
        $display("================================================================\n");

        // Initialize signals
        reset = 1;
        instruction = 0;
        stack_index = 0;
        execute = 0;
        data_in = 0;
        int_data_in = 0;
        has_memory_op = 0;
        operand_size = 2'd3;
        is_integer = 0;
        is_bcd = 0;
        control_in = 16'h037F;  // Default control word (all exceptions masked)
        control_write = 0;

        repeat(10) @(posedge clk);
        reset = 0;
        repeat(5) @(posedge clk);

        //=====================================================================
        // Test 1: FMUL LARGE * LARGE (should overflow)
        //=====================================================================
        $display("\n========================================");
        $display("Test 1: FMUL LARGE * LARGE");
        $display("========================================");

        init_fpu();
        push_value(FP80_LARGE);
        $display("Pushed FP80_LARGE: %h", FP80_LARGE);
        push_value(FP80_LARGE);
        $display("Pushed FP80_LARGE: %h", FP80_LARGE);

        execute_and_trace(INST_FMUL, 3'd1, "FMUL LARGE*LARGE", 10000);

        //=====================================================================
        // Test 2: FMUL TINY * TINY (should underflow)
        //=====================================================================
        $display("\n========================================");
        $display("Test 2: FMUL TINY * TINY");
        $display("========================================");

        init_fpu();
        push_value(FP80_TINY);
        $display("Pushed FP80_TINY: %h", FP80_TINY);
        push_value(FP80_TINY);
        $display("Pushed FP80_TINY: %h", FP80_TINY);

        execute_and_trace(INST_FMUL, 3'd1, "FMUL TINY*TINY", 10000);

        //=====================================================================
        // Test 3: FADD LARGE + LARGE (should overflow)
        //=====================================================================
        $display("\n========================================");
        $display("Test 3: FADD LARGE + LARGE");
        $display("========================================");

        init_fpu();
        push_value(FP80_LARGE);
        push_value(FP80_LARGE);

        execute_and_trace(INST_FADD, 3'd1, "FADD LARGE+LARGE", 10000);

        //=====================================================================
        // Test 4: Control test - normal multiply
        //=====================================================================
        $display("\n========================================");
        $display("Test 4: Control - FMUL 2.0 * 2.0");
        $display("========================================");

        init_fpu();
        push_value(FP80_TWO);
        push_value(FP80_TWO);

        execute_and_trace(INST_FMUL, 3'd1, "FMUL 2*2", 1000);

        //=====================================================================
        // Summary
        //=====================================================================
        $display("\n================================================================");
        $display("Debug Complete");
        $display("================================================================\n");

        #100;
        $finish;
    end

endmodule
