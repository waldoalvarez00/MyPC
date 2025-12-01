// MiSTer LED Controller for Verilator Simulation
// Provides LED register and MiSTer LED output control
//
// Features:
// - 16-bit LED register (software controlled)
// - MiSTer LED outputs (USER, POWER, DISK)
// - Activity detection for disk LED
// - PWM brightness control

module led_ctrl_sim (
    input  logic        clk,
    input  logic        rst_n,

    // CPU I/O interface for LED register
    input  logic [7:0]  io_address,     // 0=low byte, 1=high byte, 2=control
    input  logic        io_read,
    input  logic        io_write,
    input  logic [7:0]  io_writedata,
    output logic [7:0]  io_readdata,

    // Activity input (e.g., from disk controller)
    input  logic        disk_activity,

    // MiSTer LED outputs
    output logic        led_user,
    output logic [1:0]  led_power,
    output logic [1:0]  led_disk,

    // LED register output
    output logic [15:0] led_register
);

    // Control register bits
    localparam CTRL_USER_ON    = 0;   // USER LED on
    localparam CTRL_POWER_MODE = 1;   // POWER control mode
    localparam CTRL_POWER_ON   = 2;   // POWER LED on (when in user mode)
    localparam CTRL_DISK_MODE  = 3;   // DISK control mode
    localparam CTRL_DISK_ON    = 4;   // DISK LED on (when in user mode)
    localparam CTRL_PWM_EN     = 5;   // PWM enable

    // Internal registers
    reg [15:0] led_reg;
    reg [7:0]  ctrl_reg;
    reg [7:0]  pwm_level;

    // Activity detection
    reg        activity_state;
    reg [15:0] activity_counter;
    localparam ACTIVITY_DURATION = 16'd5000;  // Activity LED on duration

    // PWM counter
    reg [7:0]  pwm_counter;

    // LED register output
    assign led_register = led_reg;

    // USER LED
    assign led_user = ctrl_reg[CTRL_USER_ON];

    // POWER LED - [1]=mode, [0]=state
    assign led_power[1] = ctrl_reg[CTRL_POWER_MODE];
    assign led_power[0] = ctrl_reg[CTRL_POWER_ON];

    // DISK LED - [1]=mode, [0]=state
    // In system mode (mode=0), show activity
    // In user mode (mode=1), show user control
    assign led_disk[1] = ctrl_reg[CTRL_DISK_MODE];
    assign led_disk[0] = ctrl_reg[CTRL_DISK_MODE] ?
                         ctrl_reg[CTRL_DISK_ON] : activity_state;

    // Main logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            led_reg <= 16'h0000;
            ctrl_reg <= 8'h00;
            pwm_level <= 8'hFF;
            activity_state <= 1'b0;
            activity_counter <= 16'h0;
            pwm_counter <= 8'h0;
        end else begin
            // PWM counter
            pwm_counter <= pwm_counter + 1;

            // Activity detection
            if (disk_activity) begin
                activity_state <= 1'b1;
                activity_counter <= ACTIVITY_DURATION;
            end else if (activity_counter > 0) begin
                activity_counter <= activity_counter - 1;
                if (activity_counter == 1) begin
                    activity_state <= 1'b0;
                end
            end

            // CPU write
            if (io_write) begin
                case (io_address)
                    8'h00: led_reg[7:0] <= io_writedata;
                    8'h01: led_reg[15:8] <= io_writedata;
                    8'h02: ctrl_reg <= io_writedata;
                    8'h03: pwm_level <= io_writedata;
                    default: ;
                endcase
            end
        end
    end

    // CPU read
    always_comb begin
        case (io_address)
            8'h00: io_readdata = led_reg[7:0];
            8'h01: io_readdata = led_reg[15:8];
            8'h02: io_readdata = ctrl_reg;
            8'h03: io_readdata = pwm_level;
            8'h04: io_readdata = {6'b0, activity_state, led_user};
            default: io_readdata = 8'h00;
        endcase
    end

endmodule
