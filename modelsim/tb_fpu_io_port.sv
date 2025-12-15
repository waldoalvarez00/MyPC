// Testbench for FPU I/O Port data transfer
// Tests CPU-FPU data transfer via I/O ports

`timescale 1ns / 1ps

module tb_fpu_io_port;

    // Clock and reset
    reg clk;
    reg reset;

    // CPU I/O Bus Interface
    reg [15:0] io_addr;
    reg [15:0] io_data_out;
    wire [15:0] io_data_in;
    reg io_access;
    wire io_ack;
    reg io_wr_en;

    // FPU Data Transfer Interface
    wire fpu_data_write;
    wire fpu_data_read;
    wire [2:0] fpu_data_size;
    wire [79:0] fpu_data_out;
    reg [79:0] fpu_data_in;
    reg fpu_data_ready;

    // Test counters
    integer test_count = 0;
    integer pass_count = 0;
    integer fail_count = 0;

    // Instantiate FPU_IO_Port
    FPU_IO_Port dut (
        .clk(clk),
        .reset(reset),
        .io_addr(io_addr),
        .io_data_out(io_data_out),
        .io_data_in(io_data_in),
        .io_access(io_access),
        .io_ack(io_ack),
        .io_wr_en(io_wr_en),
        .fpu_data_write(fpu_data_write),
        .fpu_data_read(fpu_data_read),
        .fpu_data_size(fpu_data_size),
        .fpu_data_out(fpu_data_out),
        .fpu_data_in(fpu_data_in),
        .fpu_data_ready(fpu_data_ready)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    // Test procedure
    initial begin
        $display("==============================================");
        $display("FPU I/O Port Data Transfer Test");
        $display("==============================================");
        $display("");

        // Initialize signals
        reset = 1;
        io_addr = 16'h0000;
        io_data_out = 16'h0000;
        io_access = 0;
        io_wr_en = 0;
        fpu_data_in = 80'h0;
        fpu_data_ready = 0;

        // Reset sequence
        #20;
        reset = 0;
        #20;

        // Test 1: Write 80-bit data to FPU (CPU->FPU)
        $display("Test 1: Write 80-bit data to FPU (CPU->FPU)");
        test_count = test_count + 1;

        // Write data words
        io_write(16'hFFF8, 16'h1234);  // Word 0
        io_write(16'hFFFA, 16'h5678);  // Word 1
        io_write(16'hFFFC, 16'h9ABC);  // Word 2
        io_write(16'hFFFE, 16'hDEF0);  // Word 3
        io_write(16'hFFF0, 16'h1122);  // Word 4

        // Set control: size=80bit (3), direction=CPU->FPU (0)
        io_write(16'hFFF2, 16'h0003);

        // Initiate transfer
        io_write(16'hFFF4, 16'h0001);

        // Wait for transfer to process and check signals
        #20;

        // Verify write signal was asserted and data is correct
        if (fpu_data_out != 80'h1122_DEF0_9ABC_5678_1234) begin
            $display("  FAIL: Incorrect data to FPU = 0x%020x", fpu_data_out);
            $display("        Expected: 0x1122_DEF0_9ABC_5678_1234");
            fail_count = fail_count + 1;
        end else begin
            $display("  PASS: Correct 80-bit data prepared for FPU");
            pass_count = pass_count + 1;
        end

        // Simulate FPU accepting data
        fpu_data_ready = 1;
        #20;
        fpu_data_ready = 0;

        #40;

        // Test 2: Read 80-bit data from FPU (FPU->CPU)
        $display("");
        $display("Test 2: Read 80-bit data from FPU (FPU->CPU)");
        test_count = test_count + 1;

        // Prepare FPU data
        fpu_data_in = 80'hAA_BB_CC_DD_EE_FF_00_11_22_33;

        // Set control: size=80bit (3), direction=FPU->CPU (1)
        io_write(16'hFFF2, 16'h0103);  // Bit 8 = 1 for FPU->CPU

        // Initiate transfer
        io_write(16'hFFF4, 16'h0001);

        // Wait a few cycles
        #10;

        // Simulate FPU providing data
        fpu_data_ready = 1;
        #20;
        fpu_data_ready = 0;

        #20;

        // Read back data words
        // fpu_data_in = 80'hAA_BB_CC_DD_EE_FF_00_11_22_33
        // [15:0]=0x2233, [31:16]=0x0011, [47:32]=0xEEFF, [63:48]=0xCCDD, [79:64]=0xAABB
        check_io_read(16'hFFF8, 16'h2233, "Word 0");
        check_io_read(16'hFFFA, 16'h0011, "Word 1");
        check_io_read(16'hFFFC, 16'hEEFF, "Word 2");
        check_io_read(16'hFFFE, 16'hCCDD, "Word 3");
        check_io_read(16'hFFF0, 16'hAABB, "Word 4");

        #40;

        // Test 3: Write 64-bit data to FPU
        $display("");
        $display("Test 3: Write 64-bit data to FPU");
        test_count = test_count + 1;

        io_write(16'hFFF8, 16'hAAAA);  // Word 0
        io_write(16'hFFFA, 16'hBBBB);  // Word 1
        io_write(16'hFFFC, 16'hCCCC);  // Word 2
        io_write(16'hFFFE, 16'hDDDD);  // Word 3

        // Set control: size=64bit (2), direction=CPU->FPU (0)
        io_write(16'hFFF2, 16'h0002);

        // Initiate transfer
        io_write(16'hFFF4, 16'h0001);

        #10;
        fpu_data_ready = 1;
        #20;
        fpu_data_ready = 0;

        if (fpu_data_size != 3'b010) begin
            $display("  FAIL: Incorrect size = %d (expected 2)", fpu_data_size);
            fail_count = fail_count + 1;
        end else begin
            $display("  PASS: Correct 64-bit size transferred");
            pass_count = pass_count + 1;
        end

        #40;

        // Test 4: Write 32-bit data to FPU
        $display("");
        $display("Test 4: Write 32-bit data to FPU");
        test_count = test_count + 1;

        io_write(16'hFFF8, 16'h1111);  // Word 0
        io_write(16'hFFFA, 16'h2222);  // Word 1

        // Set control: size=32bit (1), direction=CPU->FPU (0)
        io_write(16'hFFF2, 16'h0001);

        // Initiate transfer
        io_write(16'hFFF4, 16'h0001);

        #10;
        fpu_data_ready = 1;
        #20;
        fpu_data_ready = 0;

        if (fpu_data_size != 3'b001) begin
            $display("  FAIL: Incorrect size = %d (expected 1)", fpu_data_size);
            fail_count = fail_count + 1;
        end else if (fpu_data_out[31:0] != 32'h2222_1111) begin
            $display("  FAIL: Incorrect data = 0x%08x", fpu_data_out[31:0]);
            fail_count = fail_count + 1;
        end else begin
            $display("  PASS: Correct 32-bit data transferred");
            pass_count = pass_count + 1;
        end

        #40;

        // Test 5: Write 16-bit data to FPU
        $display("");
        $display("Test 5: Write 16-bit data to FPU");
        test_count = test_count + 1;

        io_write(16'hFFF8, 16'h9999);  // Word 0

        // Set control: size=16bit (0), direction=CPU->FPU (0)
        io_write(16'hFFF2, 16'h0000);

        // Initiate transfer
        io_write(16'hFFF4, 16'h0001);

        #10;
        fpu_data_ready = 1;
        #20;
        fpu_data_ready = 0;

        if (fpu_data_size != 3'b000) begin
            $display("  FAIL: Incorrect size = %d (expected 0)", fpu_data_size);
            fail_count = fail_count + 1;
        end else if (fpu_data_out[15:0] != 16'h9999) begin
            $display("  FAIL: Incorrect data = 0x%04x", fpu_data_out[15:0]);
            fail_count = fail_count + 1;
        end else begin
            $display("  PASS: Correct 16-bit data transferred");
            pass_count = pass_count + 1;
        end

        #40;

        // Test 6: Check status register
        $display("");
        $display("Test 6: Check status register");
        test_count = test_count + 1;

        fpu_data_ready = 1;  // Set FPU ready
        #10;

        io_addr = 16'hFFF2;
        io_access = 1;
        io_wr_en = 0;
        #10;

        if (io_data_in[9] == 1'b1) begin  // Bit 9 = fpu_data_ready
            $display("  PASS: FPU data ready bit set correctly");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: FPU data ready bit not set");
            fail_count = fail_count + 1;
        end

        io_access = 0;
        #20;

        // Print summary
        $display("");
        $display("==============================================");
        $display("Test Summary");
        $display("==============================================");
        $display("Total Tests:  %0d", test_count);
        $display("Passed:       %0d", pass_count);
        $display("Failed:       %0d", fail_count);
        $display("Pass Rate:    %0d%%", (pass_count * 100) / test_count);
        $display("==============================================");

        if (fail_count == 0) begin
            $display("✓ ALL TESTS PASSED!");
        end else begin
            $display("✗ SOME TESTS FAILED!");
        end

        $display("==============================================");
        $finish;
    end

    // Task to perform I/O write
    task io_write(input [15:0] addr, input [15:0] data);
        begin
            @(posedge clk);
            io_addr = addr;
            io_data_out = data;
            io_access = 1;
            io_wr_en = 1;
            @(posedge clk);
            while (!io_ack) @(posedge clk);
            io_access = 0;
            io_wr_en = 0;
            @(posedge clk);
        end
    endtask

    // Task to check I/O read
    task check_io_read(input [15:0] addr, input [15:0] expected, input [127:0] name);
        reg [15:0] read_data;
        begin
            @(posedge clk);
            io_addr = addr;
            io_access = 1;
            io_wr_en = 0;
            @(posedge clk);
            while (!io_ack) @(posedge clk);
            read_data = io_data_in;
            io_access = 0;
            @(posedge clk);

            if (read_data == expected) begin
                $display("  PASS: %s = 0x%04x", name, read_data);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: %s = 0x%04x (expected 0x%04x)", name, read_data, expected);
                fail_count = fail_count + 1;
            end
            test_count = test_count + 1;
        end
    endtask

endmodule
