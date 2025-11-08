// Minimal testbench to debug VRAM read/write issue
`timescale 1ns/1ps

module vram_debug_tb;

// Clock and reset
logic clock;
logic clk_vga_cga;
logic reset;

// Memory Bus
logic memaccess;
logic [19:1] imem_m_addr;
logic [15:0] imem_m_data_in;
logic [15:0] imem_m_data_out;
logic [1:0] imem_m_bytesel;
logic imem_m_wr_en;
logic mem_m_ack;

// Converter outputs
logic [16:0] mem_addr;
logic [7:0] mem_data_in;
logic [7:0] mem_data_out;
logic mem_we;
logic mem_en;
logic [15:0] vram_data_out;

// Clock generation - 50MHz system clock
initial begin
    clock = 0;
    forever #10 clock = ~clock;  // 50MHz
end

// VGA clock - 25MHz
initial begin
    clk_vga_cga = 0;
    forever #20 clk_vga_cga = ~clk_vga_cga;  // 25MHz
end

// Reset
initial begin
    reset = 1;
    repeat(10) @(posedge clock);
    reset = 0;
end

// Bus Converter
busConverter #(.AW(14)) converter_inst (
    .outstate(),
    .clk(clock),
    .rst(reset),
    .en(memaccess),
    .we(imem_m_wr_en & memaccess),
    .data_in(imem_m_data_in),
    .data_out(vram_data_out),
    .addr(imem_m_addr[14:1]),
    .bytesel(imem_m_bytesel),
    .bus_ack(mem_m_ack),
    .mem_addr(mem_addr),
    .mem_data_in(mem_data_in),
    .mem_data_out(mem_data_out),
    .mem_we(mem_we),
    .mem_en(mem_en)
);

// VRAM
vram #(.AW(14)) vram_inst (
    .clka(clock),
    .ena(mem_en),
    .wea(mem_we),
    .addra(mem_addr),
    .dina(mem_data_out),
    .douta(mem_data_in),
    .clkb(clk_vga_cga),
    .web(1'b0),
    .enb(1'b0),
    .addrb(14'h0),
    .dinb(8'h0),
    .doutb()
);

// Output assignment
assign imem_m_data_out = memaccess ? vram_data_out : 16'h0000;

// Monitor signals going to VRAM
always @(posedge clock) begin
    if (mem_en) begin
        $display("[%0t] MONITOR: mem_en=%b, mem_we=%b, mem_addr=0x%04h, mem_data_out=0x%02h, mem_data_in=0x%02h",
                 $time, mem_en, mem_we, mem_addr, mem_data_out, mem_data_in);
    end
end

// Task: Write word to VRAM
task write_vram_word(input [15:0] addr, input [15:0] data);
    begin
        $display("[%0t] ===== WRITE TASK: addr=0x%04h, data=0x%04h =====", $time, addr, data);
        // Wait for clock edge, then set signals with small delay to avoid race
        @(posedge clock);
        #1;  // Small delay to avoid race with always @(posedge clock) blocks
        memaccess = 1'b1;
        imem_m_addr = addr[19:1];
        imem_m_data_in = data;
        imem_m_bytesel = 2'b11;
        imem_m_wr_en = 1'b1;

        @(posedge clock);  // busConverter samples signals here
        wait(mem_m_ack);
        $display("[%0t] Write ACK received", $time);

        @(posedge clock);
        memaccess = 1'b0;
        imem_m_wr_en = 1'b0;
        @(posedge clock);
        $display("[%0t] ===== WRITE TASK COMPLETE =====", $time);
    end
endtask

// Task: Read word from VRAM
task read_vram_word(input [15:0] addr, output [15:0] data);
    begin
        $display("[%0t] ===== READ TASK: addr=0x%04h =====", $time, addr);
        // Wait for clock edge, then set signals with small delay to avoid race
        @(posedge clock);
        #1;  // Small delay to avoid race with always @(posedge clock) blocks
        memaccess = 1'b1;
        imem_m_addr = addr[19:1];
        imem_m_bytesel = 2'b11;
        imem_m_wr_en = 1'b0;

        @(posedge clock);  // busConverter samples signals here
        wait(mem_m_ack);
        $display("[%0t] Read ACK received", $time);
        @(posedge clock);
        data = imem_m_data_out;
        $display("[%0t] Read data from imem_m_data_out: 0x%04h", $time, data);

        @(posedge clock);
        memaccess = 1'b0;
        @(posedge clock);
        $display("[%0t] ===== READ TASK COMPLETE: data=0x%04h =====", $time, data);
    end
endtask

// Test stimulus
logic [15:0] read_data;
initial begin
    $dumpfile("vram_debug.vcd");
    $dumpvars(0, vram_debug_tb);

    // Initialize signals
    memaccess = 0;
    imem_m_addr = 0;
    imem_m_data_in = 0;
    imem_m_bytesel = 0;
    imem_m_wr_en = 0;

    // Wait for reset
    wait(reset == 0);
    repeat(10) @(posedge clock);

    $display("\n========================================");
    $display("Starting VRAM Read/Write Test");
    $display("========================================\n");

    // Test 1: Write and read at address 0x3000
    $display("\n=== Test 1: Write 0xAA55 to address 0x3000 ===");
    write_vram_word(16'h3000, 16'hAA55);

    repeat(10) @(posedge clock);

    $display("\n=== Test 1: Read back from address 0x3000 ===");
    read_vram_word(16'h3000, read_data);

    if (read_data == 16'hAA55) begin
        $display("\n[PASS] Test 1: Read data matches written data (0xAA55)");
    end else begin
        $display("\n[FAIL] Test 1: Read data (0x%04h) != written data (0xAA55)", read_data);
    end

    repeat(10) @(posedge clock);

    // Test 2: Write and read at address 0x0000
    $display("\n=== Test 2: Write 0x1234 to address 0x0000 ===");
    write_vram_word(16'h0000, 16'h1234);

    repeat(10) @(posedge clock);

    $display("\n=== Test 2: Read back from address 0x0000 ===");
    read_vram_word(16'h0000, read_data);

    if (read_data == 16'h1234) begin
        $display("\n[PASS] Test 2: Read data matches written data (0x1234)");
    end else begin
        $display("\n[FAIL] Test 2: Read data (0x%04h) != written data (0x1234)", read_data);
    end

    repeat(10) @(posedge clock);

    $display("\n========================================");
    $display("VRAM Test Complete");
    $display("========================================\n");

    $finish;
end

// Timeout
initial begin
    #100000;  // 100us timeout
    $display("\n[ERROR] Test timeout!");
    $finish;
end

endmodule
