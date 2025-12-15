// Copyright 2024
// BIOS Upload Controller for MiSTer Integration
//
// Handles uploading BIOS ROM files from MiSTer OSD menu to on-chip BIOS RAM.
// After upload completes, BIOS becomes write-protected automatically.

`default_nettype none

module BIOSUploadController(
    input  logic        clk,
    input  logic        reset,

    // IOCTL interface from hps_io (file upload)
    input  logic        ioctl_download,  // Upload active (high during transfer)
    input  logic [15:0] ioctl_index,     // Menu index (0xC0 = BIOS upload)
    input  logic        ioctl_wr,        // Write strobe (data valid)
    input  logic [26:0] ioctl_addr,      // Byte address in file
    input  logic [15:0] ioctl_dout,      // Data word (16-bit for WIDE=1)

    // BIOS RAM write interface
    output logic        bios_wr_req,     // Write request to BIOS RAM
    output logic [13:1] bios_addr,       // Word address (up to 8K words = 16KB)
    output logic [15:0] bios_data,       // Data to write
    output logic [1:0]  bios_bytesel,    // Byte select (2'b11 = full word)

    // Status outputs
    output logic        upload_active,   // Upload in progress
    output logic        upload_complete, // Upload successfully completed
    output logic [13:0] upload_word_count // Number of words uploaded
);

    // File selector index for BIOS upload (defined in CONF_STR)
    localparam [15:0] BIOS_UPLOAD_INDEX = 16'hC0;

    // Maximum BIOS size: 16KB = 8192 words
    localparam [13:0] MAX_BIOS_WORDS = 14'd8192;

    // Internal state
    typedef enum logic [1:0] {
        IDLE,           // Waiting for upload
        UPLOADING,      // Receiving data
        VALIDATING,     // Checking upload size
        PROTECTED       // Upload complete, write-protected
    } state_t;

    state_t state, next_state;
    logic [13:0] word_count;
    logic upload_valid;

    // State machine: sequential logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            word_count <= 14'd0;
            upload_complete <= 1'b0;
            bios_wr_req <= 1'b0;
            bios_addr <= 13'd0;
            bios_data <= 16'd0;
            bios_bytesel <= 2'b00;
        end else begin
            state <= next_state;

            // Default: no write request
            bios_wr_req <= 1'b0;

            case (next_state)  // Use next_state to avoid 1-cycle latency
                IDLE: begin
                    word_count <= 14'd0;
                    upload_complete <= 1'b0;

                    if (ioctl_download && ioctl_index == BIOS_UPLOAD_INDEX) begin
                        // New upload starting - clear previous state
                        word_count <= 14'd0;
                        upload_complete <= 1'b0;
                    end
                end

                UPLOADING: begin
                    if (ioctl_wr && ioctl_addr[14:0] < 15'h4000) begin  // Within 16KB limit
                        // Write data to BIOS RAM
                        bios_wr_req <= 1'b1;
                        bios_addr <= ioctl_addr[14:1];  // Convert byte address to word address
                        bios_data <= ioctl_dout;
                        bios_bytesel <= 2'b11;  // Full word write

                        // Track highest address written
                        if (ioctl_addr[14:1] >= word_count[12:0]) begin
                            word_count <= {1'b0, ioctl_addr[14:1]} + 14'd1;
                        end
                    end
                end

                VALIDATING: begin
                    // Check if upload size is valid (must be 8KB or 16KB)
                    if (word_count == 14'd4096 || word_count == 14'd8192) begin
                        upload_complete <= 1'b1;
                    end else if (word_count > 14'd0 && word_count <= MAX_BIOS_WORDS) begin
                        // Accept any non-zero size up to 16KB (more flexible)
                        upload_complete <= 1'b1;
                    end else begin
                        // Invalid size - reject upload
                        upload_complete <= 1'b0;
                        word_count <= 14'd0;
                    end
                end

                PROTECTED: begin
                    // Write-protected state - no writes allowed
                    // Stay here until reset or new upload
                    if (ioctl_download && ioctl_index == BIOS_UPLOAD_INDEX) begin
                        // New upload requested - return to IDLE to restart
                        upload_complete <= 1'b0;
                        word_count <= 14'd0;
                    end
                end
            endcase
        end
    end

    // State machine: combinational logic (next state)
    always_comb begin
        next_state = state;

        case (state)
            IDLE: begin
                if (ioctl_download && ioctl_index == BIOS_UPLOAD_INDEX) begin
                    next_state = UPLOADING;
                end
            end

            UPLOADING: begin
                if (!ioctl_download) begin
                    // Upload ended - validate
                    next_state = VALIDATING;
                end
            end

            VALIDATING: begin
                // Always transition to PROTECTED after validation
                next_state = PROTECTED;
            end

            PROTECTED: begin
                if (ioctl_download && ioctl_index == BIOS_UPLOAD_INDEX) begin
                    // New upload requested - restart
                    next_state = IDLE;
                end
                // Otherwise stay protected
            end
        endcase
    end

    // Output assignments
    assign upload_active = (state == UPLOADING);
    assign upload_word_count = word_count;

endmodule

`default_nettype wire
