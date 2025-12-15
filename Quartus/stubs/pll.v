// Stub for Altera PLL module
// This is a simplified stub for Verilator linting purposes only

module pll (
    input refclk,
    input rst,
    output outclk_0,  // sys_clk - 30 MHz
    output outclk_1,  // vga_clk - 25.11 MHz
    output outclk_2,  // pit_clk
    output outclk_3,  // 150 MHz (SignalTap II)
    output outclk_4,  // clk_mem - 120 MHz
    output outclk_5,  // clk_uart
    output locked
);

    // Simple stub - pass through reference clock
    assign outclk_0 = refclk;
    assign outclk_1 = refclk;
    assign outclk_2 = refclk;
    assign outclk_3 = refclk;
    assign outclk_4 = refclk;
    assign outclk_5 = refclk;
    assign locked = ~rst;

endmodule
