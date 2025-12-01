//============================================================================
// InsnDecoder Testbench
// Tests x86 instruction decoding state machine
//============================================================================

`timescale 1ns/1ps

`include "../Quartus/rtl/CPU/RegisterEnum.sv"
`include "../Quartus/rtl/CPU/MicrocodeTypes.sv"
`include "../Quartus/rtl/CPU/Instruction.sv"

module insndecoder_tb;

    // Clock and reset
    reg clk;
    reg reset;

    // Control inputs
    reg flush;
    reg stall;
    reg nearly_full;

    // FIFO interface
    wire fifo_rd_en;
    reg [7:0] fifo_rd_data;
    reg fifo_empty;

    // Instruction output
    Instruction instruction;
    wire complete;

    // Immediate reader interface
    wire immed_start;
    reg immed_complete;
    wire immed_is_8bit;
    reg [15:0] immediate;

    // Test counters
    integer tests_passed = 0;
    integer tests_failed = 0;
    integer test_num = 0;

    // Instruction queue for feeding bytes
    reg [7:0] insn_queue[0:15];
    integer queue_head, queue_tail;

    // Instantiate DUT
    InsnDecoder dut (
        .clk(clk),
        .reset(reset),
        .flush(flush),
        .stall(stall),
        .nearly_full(nearly_full),
        .fifo_rd_en(fifo_rd_en),
        .fifo_rd_data(fifo_rd_data),
        .fifo_empty(fifo_empty),
        .instruction(instruction),
        .complete(complete),
        .immed_start(immed_start),
        .immed_complete(immed_complete),
        .immed_is_8bit(immed_is_8bit),
        .immediate(immediate)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // FIFO data management
    always @(*) begin
        if (queue_head != queue_tail) begin
            fifo_rd_data = insn_queue[queue_head];
            fifo_empty = 0;
        end else begin
            fifo_rd_data = 8'h00;
            fifo_empty = 1;
        end
    end

    // Advance queue on read
    always @(posedge clk) begin
        if (fifo_rd_en && !fifo_empty) begin
            queue_head <= (queue_head + 1) % 16;
        end
    end

    // Handle immediate reads
    always @(posedge clk) begin
        if (immed_start && !immed_complete) begin
            // Simulate immediate reader completing
            @(posedge clk);
            @(posedge clk);
            immed_complete <= 1;
            immediate <= immed_is_8bit ? {8'h00, insn_queue[queue_head]} :
                         {insn_queue[(queue_head+1) % 16], insn_queue[queue_head]};
        end else if (!immed_start) begin
            immed_complete <= 0;
        end
    end

    // Test tasks
    task check_pass;
        input [255:0] test_name;
    begin
        test_num = test_num + 1;
        $display("PASS: Test %0d - %s", test_num, test_name);
        tests_passed = tests_passed + 1;
    end
    endtask

    task check_fail;
        input [255:0] test_name;
        input [255:0] reason;
    begin
        test_num = test_num + 1;
        $display("FAIL: Test %0d - %s", test_num, test_name);
        $display("  Reason: %s", reason);
        tests_failed = tests_failed + 1;
    end
    endtask

    task clear_queue;
    begin
        queue_head = 0;
        queue_tail = 0;
    end
    endtask

    task push_byte;
        input [7:0] data;
    begin
        insn_queue[queue_tail] = data;
        queue_tail = (queue_tail + 1) % 16;
    end
    endtask

    task wait_for_complete;
        integer timeout;
    begin
        timeout = 0;
        while (!complete && timeout < 100) begin
            @(posedge clk);
            timeout = timeout + 1;
        end
    end
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("InsnDecoder Testbench");
        $display("========================================");

        // Initialize
        reset = 1;
        flush = 0;
        stall = 0;
        nearly_full = 0;
        immed_complete = 0;
        immediate = 16'h0000;
        queue_head = 0;
        queue_tail = 0;

        // Apply reset
        #20;
        reset = 0;
        #10;

        // Test 1: Simple 1-byte instruction (NOP = 0x90)
        clear_queue();
        push_byte(8'h90);  // NOP
        wait_for_complete();

        if (complete && instruction.opcode == 8'h90 && !instruction.has_modrm) begin
            check_pass("Simple NOP instruction");
        end else begin
            check_fail("Simple NOP instruction", "Decode failed");
        end

        // Wait for instruction to be consumed
        @(posedge clk);
        stall = 0;
        @(posedge clk);

        // Test 2: Instruction with segment override prefix
        clear_queue();
        push_byte(8'h26);  // ES: prefix
        push_byte(8'h90);  // NOP
        wait_for_complete();

        if (complete && instruction.opcode == 8'h90 && instruction.has_segment_override) begin
            check_pass("Segment override prefix (ES:)");
        end else begin
            check_fail("Segment override prefix (ES:)", "Prefix not detected");
        end

        @(posedge clk);
        @(posedge clk);

        // Test 3: Instruction with ModR/M byte (ADD r/m8, r8 = 0x00)
        clear_queue();
        push_byte(8'h00);  // ADD r/m8, r8
        push_byte(8'hC0);  // ModR/M: mod=11, reg=0, rm=0 (AL, AL)
        wait_for_complete();

        if (complete && instruction.opcode == 8'h00 && instruction.has_modrm &&
            instruction.mod_rm == 8'hC0) begin
            check_pass("Instruction with ModR/M byte");
        end else begin
            check_fail("Instruction with ModR/M byte", "ModR/M decode failed");
        end

        @(posedge clk);
        @(posedge clk);

        // Test 4: REP prefix
        clear_queue();
        push_byte(8'hF3);  // REP prefix
        push_byte(8'hA4);  // MOVSB
        wait_for_complete();

        if (complete && instruction.opcode == 8'hA4 && instruction.rep != 2'b00) begin
            check_pass("REP prefix");
        end else begin
            check_fail("REP prefix", "REP not detected");
        end

        @(posedge clk);
        @(posedge clk);

        // Test 5: LOCK prefix
        clear_queue();
        push_byte(8'hF0);  // LOCK prefix
        push_byte(8'h90);  // NOP
        wait_for_complete();

        if (complete && instruction.opcode == 8'h90 && instruction.lock) begin
            check_pass("LOCK prefix");
        end else begin
            check_fail("LOCK prefix", "LOCK not detected");
        end

        @(posedge clk);
        @(posedge clk);

        // Test 6: Flush clears state
        clear_queue();
        push_byte(8'h00);  // Start instruction
        @(posedge clk);
        @(posedge clk);
        flush = 1;
        @(posedge clk);
        flush = 0;

        if (!complete) begin
            check_pass("Flush clears decoder state");
        end else begin
            check_fail("Flush clears decoder state", "Decoder not cleared");
        end

        @(posedge clk);
        @(posedge clk);

        // Test 7: Reset clears state
        clear_queue();
        push_byte(8'h90);
        wait_for_complete();
        @(posedge clk);
        reset = 1;
        @(posedge clk);
        reset = 0;
        @(posedge clk);

        if (!complete) begin
            check_pass("Reset clears decoder state");
        end else begin
            check_fail("Reset clears decoder state", "Decoder not cleared");
        end

        // Test 8: Multiple prefixes
        clear_queue();
        push_byte(8'h26);  // ES: prefix
        push_byte(8'hF0);  // LOCK prefix
        push_byte(8'h90);  // NOP
        wait_for_complete();

        if (complete && instruction.has_segment_override && instruction.lock) begin
            check_pass("Multiple prefixes");
        end else begin
            check_fail("Multiple prefixes", "Prefixes not detected");
        end

        // Summary
        @(posedge clk);
        #20;
        $display("");
        $display("========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Total:  %0d", tests_passed + tests_failed);
        $display("Passed: %0d", tests_passed);
        $display("Failed: %0d", tests_failed);

        if (tests_failed == 0) begin
            $display("");
            $display("ALL TESTS PASSED");
        end else begin
            $display("");
            $display("SOME TESTS FAILED");
        end

        $display("========================================");
        $finish;
    end

endmodule
