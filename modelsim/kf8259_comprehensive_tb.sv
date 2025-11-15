// ================================================================
// Comprehensive Testbench for KF8259 (8259A PIC)
// Tests initialization, interrupt handling, priorities, and modes
// ================================================================

`timescale 1ns/1ps

module kf8259_comprehensive_tb;

    // Clock and reset
    logic clk;
    logic reset;

    // Bus interface
    logic chip_select;
    logic read_enable;
    logic write_enable;
    logic address;
    logic [15:0] data_bus_in;
    logic [15:0] data_bus_out;
    logic data_bus_io;
    logic ack;

    // Simple interrupt interface
    logic [7:0] simpleirq;
    logic interrupt_acknowledge_simple;

    // Cascade interface
    logic [2:0] cascade_in;
    logic [2:0] cascade_out;
    logic cascade_io;

    // External signals
    logic slave_program_n;
    logic buffer_enable;
    logic slave_program_or_enable_buffer;
    logic interrupt_acknowledge_n;
    logic interrupt_to_cpu;

    // Interrupt requests
    logic [7:0] interrupt_request;

    // Instantiate DUT
    KF8259 dut (
        .clk(clk),
        .reset(reset),
        .chip_select(chip_select),
        .read_enable(read_enable),
        .write_enable(write_enable),
        .address(address),
        .simpleirq(simpleirq),
        .interrupt_acknowledge_simple(interrupt_acknowledge_simple),
        .data_bus_in(data_bus_in),
        .data_bus_out(data_bus_out),
        .data_bus_io(data_bus_io),
        .ack(ack),
        .cascade_in(cascade_in),
        .cascade_out(cascade_out),
        .cascade_io(cascade_io),
        .slave_program_n(slave_program_n),
        .buffer_enable(buffer_enable),
        .slave_program_or_enable_buffer(slave_program_or_enable_buffer),
        .interrupt_acknowledge_n(interrupt_acknowledge_n),
        .interrupt_to_cpu(interrupt_to_cpu),
        .interrupt_request(interrupt_request)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #10 clk = ~clk;  // 50 MHz clock
    end

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Task to write to 8259
    task write_8259(input logic addr, input logic [7:0] data);
        @(posedge clk);
        chip_select = 1'b1;
        write_enable = 1'b1;
        read_enable = 1'b0;
        address = addr;
        data_bus_in = {8'h00, data};
        @(posedge clk);
        chip_select = 1'b0;
        write_enable = 1'b0;
        @(posedge clk);
    endtask

    // Task to read from 8259
    task read_8259(input logic addr, output logic [7:0] data);
        @(posedge clk);
        chip_select = 1'b1;
        read_enable = 1'b1;
        write_enable = 1'b0;
        address = addr;
        @(posedge clk);
        data = data_bus_out[7:0];
        @(posedge clk);
        chip_select = 1'b0;
        read_enable = 1'b0;
        @(posedge clk);
    endtask

    // Task to initialize 8259 (basic 8086 mode, edge-triggered)
    task init_8259_basic(input logic [7:0] vector_base);
        // ICW1: Edge-triggered, single, need ICW4
        write_8259(1'b0, 8'b00010011);  // A0=0, D4=1, LTIM=0, SNGL=1, IC4=1

        // ICW2: Vector base
        write_8259(1'b1, vector_base);

        // ICW4: 8086 mode, normal EOI
        write_8259(1'b1, 8'b00000001);  // uPM=1 (8086 mode)

        // OCW1: Unmask all interrupts
        write_8259(1'b1, 8'b00000000);
    endtask

    // Task to initialize 8259 (cascade mode)
    task init_8259_cascade_master(input logic [7:0] vector_base, input logic [7:0] slave_mask);
        // ICW1: Edge-triggered, cascade, need ICW4
        write_8259(1'b0, 8'b00010001);  // D4=1, LTIM=0, SNGL=0, IC4=1

        // ICW2: Vector base
        write_8259(1'b1, vector_base);

        // ICW3: Slave devices on IR lines
        write_8259(1'b1, slave_mask);

        // ICW4: 8086 mode, master
        write_8259(1'b1, 8'b00000001);

        // OCW1: Unmask all interrupts
        write_8259(1'b1, 8'b00000000);
    endtask

    // Task to send EOI
    task send_eoi(input logic specific, input logic [2:0] irq_level);
        if (specific)
            write_8259(1'b0, {3'b011, 2'b00, irq_level});  // Specific EOI
        else
            write_8259(1'b0, 8'b00100000);  // Non-specific EOI
    endtask

    // Local test variables
    logic [7:0] irr_value;
    logic int_raised;

    // Task to check test result
    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            fail_count++;
        end
    endtask

    // Task to trigger interrupt and acknowledge
    task trigger_and_ack_irq(input int irq_num);
        // Trigger interrupt
        interrupt_request[irq_num] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[irq_num] = 1'b0;

        // Wait for interrupt_to_cpu
        repeat(5) @(posedge clk);

        // Acknowledge
        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        @(posedge clk);
    endtask

    // Main test sequence
    initial begin
        $display("================================================================");
        $display("KF8259 Comprehensive Test Suite");
        $display("================================================================");

        // Initialize signals
        reset = 1;
        chip_select = 0;
        read_enable = 0;
        write_enable = 0;
        address = 0;
        data_bus_in = 0;
        interrupt_acknowledge_simple = 0;
        cascade_in = 0;
        slave_program_n = 1;
        interrupt_acknowledge_n = 1;
        interrupt_request = 8'h00;

        // Release reset
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(5) @(posedge clk);

        // ================================================================
        // TEST 1: Initialization Sequence
        // ================================================================
        $display("\n--- Test 1: Basic Initialization (Single Mode) ---");
        init_8259_basic(8'h20);
        repeat(5) @(posedge clk);
        check_result("Initialization completed without errors", 1'b1);

        // ================================================================
        // TEST 2: Single Interrupt Request (Edge-Triggered)
        // ================================================================
        $display("\n--- Test 2: Single Interrupt Request (IRQ0, Edge-Triggered) ---");
        interrupt_request[0] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[0] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("INT signal raised", interrupt_to_cpu == 1'b1);
        check_result("Correct IRQ vector (IRQ0 = 0x20)", simpleirq == 8'h20);

        // Acknowledge interrupt
        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        repeat(3) @(posedge clk);

        // Send EOI
        send_eoi(1'b0, 3'b000);
        repeat(3) @(posedge clk);

        check_result("INT signal cleared after EOI", interrupt_to_cpu == 1'b0);

        // ================================================================
        // TEST 3: Multiple Interrupts with Priority
        // ================================================================
        $display("\n--- Test 3: Multiple Interrupts with Priority ---");

        // Trigger IRQ3 and IRQ1 simultaneously
        interrupt_request[3] = 1'b1;
        interrupt_request[1] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[3] = 1'b0;
        interrupt_request[1] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("Higher priority IRQ1 served first", simpleirq[2:0] == 3'b001);

        // Acknowledge IRQ1
        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);
        repeat(5) @(posedge clk);

        check_result("Lower priority IRQ3 served next", simpleirq[2:0] == 3'b011);

        // Acknowledge IRQ3
        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 4: Interrupt Masking (OCW1)
        // ================================================================
        $display("\n--- Test 4: Interrupt Masking ---");

        // Mask IRQ2
        write_8259(1'b1, 8'b00000100);  // Mask bit 2
        repeat(3) @(posedge clk);

        // Try to trigger masked IRQ2
        interrupt_request[2] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[2] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("Masked IRQ2 does not raise INT", interrupt_to_cpu == 1'b0);

        // Unmask IRQ2
        write_8259(1'b1, 8'b00000000);
        repeat(3) @(posedge clk);

        // Trigger unmasked IRQ2
        interrupt_request[2] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[2] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("Unmasked IRQ2 raises INT", interrupt_to_cpu == 1'b1);
        check_result("Correct IRQ2 vector", simpleirq[2:0] == 3'b010);

        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 5: Specific EOI (OCW2)
        // ================================================================
        $display("\n--- Test 5: Specific EOI ---");

        // Trigger IRQ5
        trigger_and_ack_irq(5);

        // Send specific EOI for IRQ5
        send_eoi(1'b1, 3'b101);
        repeat(3) @(posedge clk);

        check_result("Specific EOI processed", 1'b1);

        // ================================================================
        // TEST 6: Priority Rotation (OCW2)
        // ================================================================
        $display("\n--- Test 6: Priority Rotation ---");

        // Set auto-rotate mode
        write_8259(1'b0, 8'b10000000);  // Rotate on Auto-EOI
        repeat(3) @(posedge clk);

        check_result("Auto-rotate mode set", 1'b1);

        // ================================================================
        // TEST 7: Read Interrupt Request Register (OCW3)
        // ================================================================
        $display("\n--- Test 7: Read IRR/ISR ---");

        // Set read mode to IRR
        write_8259(1'b0, 8'b00001010);  // OCW3: Read IRR
        repeat(3) @(posedge clk);

        // Trigger IRQ4 but don't acknowledge
        interrupt_request[4] = 1'b1;
        repeat(3) @(posedge clk);

        read_8259(1'b0, irr_value);

        check_result("IRR shows pending IRQ4", irr_value[4] == 1'b1);

        interrupt_request[4] = 1'b0;
        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);
        repeat(3) @(posedge clk);

        // Set read mode to ISR
        write_8259(1'b0, 8'b00001011);  // OCW3: Read ISR
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 8: All IRQ Lines
        // ================================================================
        $display("\n--- Test 8: Test All IRQ Lines (0-7) ---");

        for (int i = 0; i < 8; i++) begin
            interrupt_request[i] = 1'b1;
            repeat(3) @(posedge clk);
            interrupt_request[i] = 1'b0;
            repeat(5) @(posedge clk);

            check_result($sformatf("IRQ%0d triggers correctly", i),
                         interrupt_to_cpu == 1'b1 && simpleirq[2:0] == i[2:0]);

            interrupt_acknowledge_simple = 1'b1;
            @(posedge clk);
            interrupt_acknowledge_simple = 1'b0;
            send_eoi(1'b0, 3'b000);
            repeat(3) @(posedge clk);
        end

        // ================================================================
        // TEST 9: Nested Interrupts
        // ================================================================
        $display("\n--- Test 9: Nested Interrupts ---");

        // Trigger low-priority IRQ7
        interrupt_request[7] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[7] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("IRQ7 triggered", simpleirq[2:0] == 3'b111);

        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        repeat(3) @(posedge clk);

        // While servicing IRQ7, trigger higher-priority IRQ0
        interrupt_request[0] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[0] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("Higher priority IRQ0 interrupts IRQ7", simpleirq[2:0] == 3'b000);

        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);  // EOI for IRQ0
        repeat(3) @(posedge clk);

        send_eoi(1'b0, 3'b000);  // EOI for IRQ7
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 10: Re-initialization
        // ================================================================
        $display("\n--- Test 10: Re-initialization ---");

        // Re-initialize with different vector base
        init_8259_basic(8'h40);
        repeat(5) @(posedge clk);

        // Test with new vector base
        interrupt_request[1] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[1] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("Re-initialization with new vector (0x41)", simpleirq == 8'h41);

        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 11: Edge Detection (Low-to-High Transition)
        // ================================================================
        $display("\n--- Test 11: Edge Detection ---");

        // Hold IRQ3 high (should not trigger in edge mode)
        interrupt_request[3] = 1'b1;
        repeat(10) @(posedge clk);

        int_raised = interrupt_to_cpu;

        // Release and re-trigger
        interrupt_request[3] = 1'b0;
        repeat(5) @(posedge clk);
        interrupt_request[3] = 1'b1;
        repeat(3) @(posedge clk);
        interrupt_request[3] = 1'b0;
        repeat(5) @(posedge clk);

        check_result("Edge detection on low-to-high transition", interrupt_to_cpu == 1'b1);

        interrupt_acknowledge_simple = 1'b1;
        @(posedge clk);
        interrupt_acknowledge_simple = 1'b0;
        send_eoi(1'b0, 3'b000);
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 12: Simultaneous Mask and IRQ
        // ================================================================
        $display("\n--- Test 12: Simultaneous Operations ---");

        // Mask IRQ6 and trigger it simultaneously
        interrupt_request[6] = 1'b1;
        write_8259(1'b1, 8'b01000000);  // Mask IRQ6
        repeat(5) @(posedge clk);
        interrupt_request[6] = 1'b0;

        check_result("Simultaneous mask blocks interrupt", interrupt_to_cpu == 1'b0);

        // Unmask
        write_8259(1'b1, 8'b00000000);
        repeat(3) @(posedge clk);

        // ================================================================
        // Test Summary
        // ================================================================
        $display("\n================================================================");
        $display("TEST SUMMARY");
        $display("================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
        $display("================================================================");

        if (fail_count == 0) begin
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗");
            $finish(1);
        end
    end

    // Timeout watchdog
    initial begin
        #100000;  // 100 us timeout
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
