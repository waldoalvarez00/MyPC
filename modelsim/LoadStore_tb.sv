//============================================================================
// LoadStore Testbench
// Tests memory load/store unit with aligned/unaligned accesses
//============================================================================

`timescale 1ns/1ps

module loadstore_tb;

    // Clock and reset
    reg clk;
    reg reset;

    // MAR inputs
    reg write_mar;
    reg [15:0] segment;
    reg [15:0] mar_in;

    // MDR inputs
    reg write_mdr;
    reg [15:0] mdr_in;

    // Memory bus outputs
    wire [19:1] m_addr;
    wire [15:0] m_data_out;
    wire m_access;
    wire m_wr_en;
    wire [1:0] m_bytesel;

    // Memory bus inputs
    reg [15:0] m_data_in;
    reg m_ack;

    // Control signals
    reg io;
    reg mem_read;
    reg mem_write;
    reg is_8bit;
    reg wr_en;

    // Outputs
    wire [15:0] mar_out;
    wire [15:0] mdr_out;
    wire busy;

    // Test counters
    integer tests_passed = 0;
    integer tests_failed = 0;
    integer test_num = 0;

    // Instantiate DUT
    LoadStore dut (
        .clk(clk),
        .reset(reset),
        .write_mar(write_mar),
        .segment(segment),
        .mar_in(mar_in),
        .mar_out(mar_out),
        .mdr_out(mdr_out),
        .write_mdr(write_mdr),
        .mdr_in(mdr_in),
        .m_addr(m_addr),
        .m_data_in(m_data_in),
        .m_data_out(m_data_out),
        .m_access(m_access),
        .m_ack(m_ack),
        .m_wr_en(m_wr_en),
        .m_bytesel(m_bytesel),
        .io(io),
        .mem_read(mem_read),
        .mem_write(mem_write),
        .is_8bit(is_8bit),
        .wr_en(wr_en),
        .busy(busy)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
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

    task write_mar_value;
        input [15:0] seg;
        input [15:0] addr;
    begin
        @(posedge clk);
        segment = seg;
        mar_in = addr;
        write_mar = 1;
        @(posedge clk);
        write_mar = 0;
    end
    endtask

    task write_mdr_value;
        input [15:0] data;
    begin
        @(posedge clk);
        mdr_in = data;
        write_mdr = 1;
        @(posedge clk);
        write_mdr = 0;
    end
    endtask

    task wait_for_access;
        integer timeout;
    begin
        timeout = 0;
        // Wait for first clock where FSM sees the request
        @(posedge clk);
        #1;  // Allow non-blocking assignments to settle
        while (!m_access && timeout < 100) begin
            @(posedge clk);
            #1;
            timeout = timeout + 1;
        end
    end
    endtask

    task send_ack;
    begin
        @(posedge clk);
        m_ack = 1;
        @(posedge clk);
        m_ack = 0;
    end
    endtask

    task wait_not_busy;
        integer timeout;
    begin
        timeout = 0;
        while (busy && timeout < 100) begin
            @(posedge clk);
            timeout = timeout + 1;
        end
    end
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("LoadStore Testbench");
        $display("========================================");

        // Initialize
        reset = 1;
        write_mar = 0;
        segment = 16'h0000;
        mar_in = 16'h0000;
        write_mdr = 0;
        mdr_in = 16'h0000;
        m_data_in = 16'h0000;
        m_ack = 0;
        io = 0;
        mem_read = 0;
        mem_write = 0;
        is_8bit = 0;
        wr_en = 0;

        // Apply reset
        #20;
        reset = 0;
        #10;

        // Test 1: Write MAR and check output
        write_mar_value(16'h1000, 16'h0100);
        if (mar_out == 16'h0100)
            check_pass("MAR write and readback");
        else
            check_fail("MAR write and readback", "MAR value mismatch");

        // Test 2: Aligned 16-bit read
        write_mar_value(16'h0000, 16'h0100);
        @(posedge clk);
        mem_read = 1;
        is_8bit = 0;
        wait_for_access();

        if (m_access && !m_wr_en && m_bytesel == 2'b11) begin
            m_data_in = 16'hABCD;
            send_ack();
            wait_not_busy();
            mem_read = 0;

            if (mdr_out == 16'hABCD)
                check_pass("Aligned 16-bit read");
            else
                check_fail("Aligned 16-bit read", "Data mismatch");
        end else begin
            mem_read = 0;
            check_fail("Aligned 16-bit read", "Access signals incorrect");
        end

        // Test 3: Aligned 8-bit read
        write_mar_value(16'h0000, 16'h0200);
        @(posedge clk);
        mem_read = 1;
        is_8bit = 1;
        wait_for_access();

        if (m_access && !m_wr_en && m_bytesel == 2'b01) begin
            m_data_in = 16'h00EF;
            send_ack();
            wait_not_busy();
            mem_read = 0;

            if (mdr_out[7:0] == 8'hEF)
                check_pass("Aligned 8-bit read");
            else
                check_fail("Aligned 8-bit read", "Data mismatch");
        end else begin
            mem_read = 0;
            check_fail("Aligned 8-bit read", "Access signals incorrect");
        end

        // Test 4: Aligned 16-bit write
        write_mar_value(16'h0000, 16'h0300);
        write_mdr_value(16'h1234);
        @(posedge clk);
        mem_write = 1;
        is_8bit = 0;
        wait_for_access();

        if (m_access && m_wr_en && m_bytesel == 2'b11 && m_data_out == 16'h1234) begin
            send_ack();
            wait_not_busy();
            mem_write = 0;
            check_pass("Aligned 16-bit write");
        end else begin
            mem_write = 0;
            check_fail("Aligned 16-bit write", "Access signals or data incorrect");
        end

        // Test 5: Aligned 8-bit write
        write_mar_value(16'h0000, 16'h0400);
        write_mdr_value(16'h00AB);
        @(posedge clk);
        mem_write = 1;
        is_8bit = 1;
        wait_for_access();

        if (m_access && m_wr_en && m_bytesel == 2'b01) begin
            send_ack();
            wait_not_busy();
            mem_write = 0;
            check_pass("Aligned 8-bit write");
        end else begin
            mem_write = 0;
            check_fail("Aligned 8-bit write", "Access signals incorrect");
        end

        // Test 6: Physical address calculation
        // Segment 0x1000, offset 0x0100 -> physical = 0x10000 + 0x0100 = 0x10100
        // Word address = 0x10100 >> 1 = 0x8080
        write_mar_value(16'h1000, 16'h0100);
        @(posedge clk);
        mem_read = 1;
        is_8bit = 0;
        wait_for_access();

        // Expected: segment << 4 + offset = 0x10000 + 0x0100 = 0x10100
        // Word addr = 0x10100 >> 1 = 0x8080
        if (m_addr == 19'h8080) begin
            send_ack();
            wait_not_busy();
            mem_read = 0;
            check_pass("Physical address calculation");
        end else begin
            mem_read = 0;
            $display("FAIL: Test %0d - Physical address calculation", test_num + 1);
            $display("  Expected: 0x8080, got 0x%05x", m_addr);
            test_num = test_num + 1;
            tests_failed = tests_failed + 1;
        end

        // Test 7: I/O read
        write_mar_value(16'h0000, 16'h03F8);  // COM1 port
        @(posedge clk);
        io = 1;
        mem_read = 1;
        is_8bit = 1;
        wait_for_access();

        if (m_access && !m_wr_en) begin
            m_data_in = 16'h00FF;
            send_ack();
            wait_not_busy();
            mem_read = 0;
            io = 0;

            if (mdr_out[7:0] == 8'hFF)
                check_pass("I/O read");
            else
                check_fail("I/O read", "Data mismatch");
        end else begin
            mem_read = 0;
            io = 0;
            check_fail("I/O read", "Access signals incorrect");
        end

        // Test 8: I/O write
        write_mar_value(16'h0000, 16'h03F8);
        write_mdr_value(16'h00AA);
        @(posedge clk);
        io = 1;
        mem_write = 1;
        is_8bit = 1;
        wait_for_access();

        if (m_access && m_wr_en) begin
            send_ack();
            wait_not_busy();
            mem_write = 0;
            io = 0;
            check_pass("I/O write");
        end else begin
            mem_write = 0;
            io = 0;
            check_fail("I/O write", "Access signals incorrect");
        end

        // Test 9: Unaligned 16-bit read (requires two bus cycles)
        write_mar_value(16'h0000, 16'h0101);  // Odd address
        @(posedge clk);
        mem_read = 1;
        is_8bit = 0;

        // First byte (high byte of first word)
        wait_for_access();
        if (m_access && m_bytesel == 2'b10) begin
            m_data_in = 16'hAB00;  // High byte = 0xAB
            send_ack();
        end

        // Second byte (low byte of next word)
        wait_for_access();
        if (m_access && m_bytesel == 2'b01) begin
            m_data_in = 16'h00CD;  // Low byte = 0xCD
            send_ack();
            wait_not_busy();
            mem_read = 0;

            // Result should be 0xCDAB (little endian: low=AB, high=CD)
            if (mdr_out == 16'hCDAB) begin
                check_pass("Unaligned 16-bit read");
            end else begin
                $display("FAIL: Test %0d - Unaligned 16-bit read", test_num + 1);
                $display("  Expected: 0xCDAB, got 0x%04x", mdr_out);
                test_num = test_num + 1;
                tests_failed = tests_failed + 1;
            end
        end else begin
            mem_read = 0;
            check_fail("Unaligned 16-bit read", "Second access incorrect");
        end

        // Test 10: Reset during operation
        write_mar_value(16'h0000, 16'h0500);
        @(posedge clk);
        mem_read = 1;
        wait_for_access();
        @(posedge clk);
        reset = 1;
        mem_read = 0;  // Clear request before checking
        @(posedge clk);
        reset = 0;
        @(posedge clk);  // Allow state to settle
        #1;

        if (!busy)
            check_pass("Reset during operation");
        else
            check_fail("Reset during operation", "Still busy after reset");

        // Summary
        @(posedge clk);
        #10;
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
