module TriggerAfterNHigh(
    input wire clk,           // Clock input
    input wire rst,           // Asynchronous reset input
    input wire signal_in,     // Input signal to monitor
    output reg trigger        // Output trigger
);

parameter N = 10; // Define N, the duration the input signal needs to be high

// Counter to track the number of consecutive high clock ticks
reg [31:0] counter;

always @(posedge clk or posedge rst) begin

    if (rst) begin
        // Reset counter and trigger to 0 on reset
        counter <= 0;
        trigger <= 0;
    end
    else if (signal_in) begin
        // Increment counter if signal_in is high
        counter <= counter + 1;
        if (counter >= N - 1) begin
            // Set trigger to 1 if counter has reached N consecutive ticks
            trigger <= 1;
        end
    end
    else begin
        // Reset counter if signal_in goes low
        counter <= 0;
        trigger <= 0;
    end
	 
end

endmodule
