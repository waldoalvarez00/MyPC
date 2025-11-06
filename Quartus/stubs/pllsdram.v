// Stub for Altera SDRAM PLL module
// This is a simplified stub for Verilator linting purposes only

module pllsdram (
    input refclk,
    input rst,
    output outclk_0,  // 80 MHz
    output outclk_1,  // 80 MHz
    output locked
);

    // Simple stub - pass through reference clock
    assign outclk_0 = refclk;
    assign outclk_1 = refclk;
    assign locked = ~rst;

endmodule
