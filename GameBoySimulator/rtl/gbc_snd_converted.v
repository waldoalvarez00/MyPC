//
// GameBoy Sound (APU) - Converted from VHDL to Verilog
//
// Original: gbc_snd.vhd from MiSTer GameBoy core
// Converted for Verilator simulation
//
// Notes:
//   When the output DAC of each channel is disabled, the real voltage will drift
//   to 0 V at some unknown rate. Here, it is implemented as a gradual decay.
//

module gbc_snd (
    input         clk,
    input         ce,
    input         reset,

    input         is_gbc,
    input         remove_pops,  // 0: Accurate output, 1: Toggling DACs will not cause pops

    input         s1_read,
    input         s1_write,
    input  [6:0]  s1_addr,
    output reg [7:0] s1_readdata,
    input  [7:0]  s1_writedata,

    output reg [15:0] snd_left,
    output reg [15:0] snd_right,

    // Savestates (stubbed out for simulation)
    input  [63:0] SaveStateBus_Din,
    input  [9:0]  SaveStateBus_Adr,
    input         SaveStateBus_wren,
    input         SaveStateBus_rst,
    output [63:0] SaveStateBus_Dout
);

// Savestate stub - return zeros
assign SaveStateBus_Dout = 64'h0;

// Wave RAM type
reg [3:0] wav_ram [0:31];

// Enable signals
reg        en_snd;            // Enable at base sound frequency (4.19MHz)
reg        en_snd2;           // Enable at clk/2
reg        en_snd4;           // Enable at clk/4
reg        en_512;            // 512Hz enable

reg        en_snden2;         // Enable at clk/2
reg        en_snden4;         // Enable at clk/4

reg        en_len;            // Sample length
reg        en_len_r;
reg        en_env;            // Envelope
reg        en_sweep;          // Sweep

reg        snd_enable;

// Square 1 signals
reg  [2:0] sq1_swper;         // Sweep period
reg        sq1_swdir;         // Sweep direction
reg        sq1_swdir_change;  // Sweep direction-change
reg  [2:0] sq1_swshift;       // Sweep frequency shift
reg  [1:0] sq1_duty;          // Duty cycle
reg  [6:0] sq1_slen;          // Play length
reg  [3:0] sq1_svol;          // Initial volume
reg        sq1_out;
reg        sq1_envsgn;        // Envelope sign
reg        sq1_envsgn_old;    // Old envelope sign (zombie mode)
reg  [2:0] sq1_envper;        // Envelope period
reg  [2:0] sq1_envper_old;    // Old envelope period (zombie mode)
reg [10:0] sq1_freq;          // Frequency
reg        sq1_trigger;       // Trigger play note
reg        sq1_lenchk;        // Length check enable
reg        sq1_len_en_change; // Length off -> on
reg [10:0] sq1_fr2;           // Frequency shadow copy
reg  [3:0] sq1_vol;           // Volume
reg        sq1_nr2change;
reg        sq1_lenchange;
reg        sq1_lenquirk;
reg        sq1_freqchange;
reg        sq1_playing;       // Channel active
reg  [3:0] sq1_wav;           // Output waveform
reg        sq1_suppressed;    // 1st sample suppressed when triggered after poweron
reg        sq1_dac_en;

// Square 2 signals
reg        sq2_out;
reg  [1:0] sq2_duty;
reg  [6:0] sq2_slen;
reg  [3:0] sq2_svol;
reg        sq2_nr2change;
reg        sq2_lenchange;
reg        sq2_lenquirk;
reg        sq2_envsgn;
reg  [2:0] sq2_envper;
reg        sq2_envsgn_old;
reg  [2:0] sq2_envper_old;
reg [10:0] sq2_freq;
reg        sq2_trigger;
reg        sq2_lenchk;
reg  [3:0] sq2_vol;
reg        sq2_playing;
reg  [3:0] sq2_wav;
reg        sq2_suppressed;
reg        sq2_dac_en;

// Wave channel signals
reg        wav_enable;
reg  [8:0] wav_slen;
reg        wav_lenchange;
reg        wav_lenquirk;
reg  [1:0] wav_volsh;
reg [10:0] wav_freq;
reg        wav_trigger;
reg        wav_lenchk;
reg  [4:0] wav_index;
reg  [1:0] wav_access;
reg        wav_playing;
reg  [3:0] wav_wav;
reg  [3:0] wav_wav_r;

// Noise channel signals
reg  [6:0] noi_slen;
reg        noi_lenchange;
reg        noi_lenquirk;
reg  [3:0] noi_svol;
reg        noi_nr2change;
reg        noi_envsgn;
reg  [2:0] noi_envper;
reg        noi_envsgn_old;
reg  [2:0] noi_envper_old;
reg  [3:0] noi_freqsh;
reg        noi_freqchange;
reg        noi_short;
reg  [2:0] noi_div;
reg        noi_trigger;
reg        noi_lenchk;
reg  [3:0] noi_vol;
reg        noi_playing;
reg  [3:0] noi_wav;
reg        noi_dac_en;

// Control signals
reg [7:0]  ch_map;
reg [7:0]  ch_vol;
reg [2:0]  framecnt;

// Trigger edge detection
reg        sq1_trigger_r;
reg        sq2_trigger_r;
reg        wav_trigger_r;
reg        noi_trigger_r;
reg        s1_write_r;

// DAC outputs
wire signed [8:0] sq1_dac_out;
wire signed [8:0] sq2_dac_out;
wire signed [8:0] wav_dac_out;
wire signed [8:0] noi_dac_out;

// Derived enables
always @(*) begin
    en_snd2 = en_snd & en_snden2;
    en_snd4 = en_snd & en_snden4;
end

// Base clock enable generation
always @(posedge clk) begin
    if (reset) begin
        en_snd <= 1'b0;
    end else if (ce) begin
        en_snd <= ~en_snd;
    end
end

// Frame sequencer clock enable generation
reg [1:0] clkcnt;
reg [12:0] cnt_512;

always @(posedge clk) begin
    if (reset) begin
        clkcnt <= 2'b00;
        cnt_512 <= 13'd0;
        framecnt <= 3'd0;
        en_len_r <= 1'b0;
        en_snden2 <= 1'b0;
        en_snden4 <= 1'b0;
        en_len <= 1'b0;
        en_env <= 1'b0;
        en_sweep <= 1'b0;
        en_512 <= 1'b0;
    end else if (snd_enable == 1'b0) begin
        // Only clock frame sequencer if sound is enabled
        clkcnt <= 2'b00;
        cnt_512 <= 13'd0;
        framecnt <= 3'd0;
        en_len_r <= 1'b0;
        en_snden2 <= 1'b0;
        en_snden4 <= 1'b0;
        en_len <= 1'b0;
        en_env <= 1'b0;
        en_sweep <= 1'b0;
        en_512 <= 1'b0;
    end else if (ce) begin
        // Base clock divider
        if (en_snd) begin
            clkcnt <= clkcnt + 1'b1;
            en_snden2 <= clkcnt[0];
            en_snden4 <= (clkcnt == 2'b11);
        end

        // Frame sequencer clock enables
        en_len <= 1'b0;
        en_env <= 1'b0;
        en_sweep <= 1'b0;

        if (en_512) begin
            en_len_r <= ~en_len_r;
            if (framecnt == 0 || framecnt == 2 || framecnt == 4 || framecnt == 6) begin
                en_len <= 1'b1;
                en_len_r <= ~en_len_r;
            end
            if (framecnt == 2 || framecnt == 6) begin
                en_sweep <= 1'b1;
            end
            if (framecnt == 7) begin
                en_env <= 1'b1;
            end
            if (framecnt < 7)
                framecnt <= framecnt + 1'b1;
            else
                framecnt <= 3'd0;
        end

        // 512 Hz enable
        en_512 <= 1'b0;
        if (en_snd) begin
            if (cnt_512 == 13'h1FFF) begin
                cnt_512 <= 13'd0;
                en_512 <= 1'b1;
            end else begin
                cnt_512 <= cnt_512 + 1'b1;
            end
        end
    end
end

// Register write process
reg [2:0] sq1_trigger_cnt;
reg [2:0] sq2_trigger_cnt;
reg [2:0] noi_trigger_cnt;
reg [1:0] wav_trigger_cnt;

always @(posedge clk) begin
    integer k;
    if (reset) begin
        sq1_swper <= 3'd0;
        sq1_swdir <= 1'b0;
        sq1_swshift <= 3'd0;
        sq1_duty <= 2'd0;
        sq1_slen <= 7'd0;
        sq1_svol <= 4'd0;
        sq1_envsgn <= 1'b0;
        sq1_envper <= 3'd0;
        sq1_freq <= 11'd0;
        sq1_lenchk <= 1'b0;
        sq1_trigger <= 1'b0;

        sq2_duty <= 2'd0;
        sq2_slen <= 7'd0;
        sq2_svol <= 4'd0;
        sq2_envsgn <= 1'b0;
        sq2_envper <= 3'd0;
        sq2_freq <= 11'd0;
        sq2_lenchk <= 1'b0;
        sq2_trigger <= 1'b0;

        wav_enable <= 1'b0;
        wav_volsh <= 2'd0;
        wav_freq <= 11'd0;
        wav_trigger <= 1'b0;
        wav_lenchk <= 1'b0;
        wav_slen <= 9'd0;

        noi_slen <= 7'd0;
        noi_svol <= 4'd0;
        noi_envsgn <= 1'b0;
        noi_envper <= 3'd0;
        noi_freqsh <= 4'd0;
        noi_short <= 1'b0;
        noi_div <= 3'd0;
        noi_trigger <= 1'b0;
        noi_lenchk <= 1'b0;

        ch_map <= 8'd0;
        ch_vol <= 8'd0;
        snd_enable <= 1'b0;

        sq1_trigger_cnt <= 3'd0;
        sq2_trigger_cnt <= 3'd0;
        wav_trigger_cnt <= 2'd0;
        noi_trigger_cnt <= 3'd0;

        s1_write_r <= 1'b0;

        // Initialize wave RAM
        for (k = 0; k < 32; k = k + 1) begin
            wav_ram[k] <= 4'd0;
        end
    end else if (ce) begin
        // Trigger countdown
        if (en_snd2) begin
            if (sq1_trigger_cnt == 3'd0)
                sq1_trigger <= 1'b0;
            else
                sq1_trigger_cnt <= sq1_trigger_cnt - 1'b1;

            if (sq2_trigger_cnt == 3'd0)
                sq2_trigger <= 1'b0;
            else
                sq2_trigger_cnt <= sq2_trigger_cnt - 1'b1;

            if (wav_trigger_cnt == 2'd0)
                wav_trigger <= 1'b0;
            else
                wav_trigger_cnt <= wav_trigger_cnt - 1'b1;

            if (noi_trigger_cnt == 3'd0)
                noi_trigger <= 1'b0;
            else
                noi_trigger_cnt <= noi_trigger_cnt - 1'b1;
        end

        sq2_nr2change <= 1'b0;
        sq1_nr2change <= 1'b0;
        noi_nr2change <= 1'b0;
        noi_freqchange <= 1'b0;

        sq2_lenchange <= 1'b0;
        sq1_lenchange <= 1'b0;
        wav_lenchange <= 1'b0;
        noi_lenchange <= 1'b0;
        sq1_lenquirk <= 1'b0;
        sq2_lenquirk <= 1'b0;
        wav_lenquirk <= 1'b0;
        noi_lenquirk <= 1'b0;
        sq1_swdir_change <= 1'b0;

        if (sq1_freqchange)
            sq1_freq <= sq1_fr2;

        s1_write_r <= s1_write;

        // Register writes (ignored when APU off except NR52 and wave RAM)
        if (s1_write && !s1_write_r &&
            (snd_enable || s1_addr == 7'b0100110 || s1_addr[5:4] == 2'b11 ||
             (!is_gbc && (s1_addr == 7'b0010001 || s1_addr == 7'b0010110 ||
                          s1_addr == 7'b0011011 || s1_addr == 7'b0100000)))) begin

            case (s1_addr)
                // Square 1
                7'b0010000: begin // NR10 FF10
                    sq1_swper <= s1_writedata[6:4];
                    if (s1_writedata[3] == 1'b0)
                        sq1_swdir_change <= 1'b1;
                    sq1_swdir <= s1_writedata[3];
                    sq1_swshift <= s1_writedata[2:0];
                end
                7'b0010001: begin // NR11 FF11
                    if (snd_enable)
                        sq1_duty <= s1_writedata[7:6];
                    sq1_slen <= 7'd64 - {1'b0, s1_writedata[5:0]};
                    sq1_lenchange <= 1'b1;
                end
                7'b0010010: begin // NR12 FF12
                    sq1_envsgn_old <= sq1_envsgn;
                    sq1_envper_old <= sq1_envper;
                    sq1_nr2change <= 1'b1;
                    sq1_svol <= s1_writedata[7:4];
                    sq1_envsgn <= s1_writedata[3];
                    sq1_envper <= s1_writedata[2:0];
                end
                7'b0010011: begin // NR13 FF13
                    sq1_freq[7:0] <= s1_writedata;
                end
                7'b0010100: begin // NR14 FF14
                    sq1_trigger <= s1_writedata[7];
                    if (s1_writedata[7]) begin
                        if (sq1_playing)
                            sq1_trigger_cnt <= 3'd2;
                        else
                            sq1_trigger_cnt <= 3'd4;
                    end
                    if (!sq1_lenchk && s1_writedata[6] && en_len_r)
                        sq1_lenquirk <= 1'b1;
                    sq1_lenchk <= s1_writedata[6];
                    sq1_freq[10:8] <= s1_writedata[2:0];
                end

                // Square 2
                7'b0010110: begin // NR21 FF16
                    if (snd_enable)
                        sq2_duty <= s1_writedata[7:6];
                    sq2_slen <= 7'd64 - {1'b0, s1_writedata[5:0]};
                    sq2_lenchange <= 1'b1;
                end
                7'b0010111: begin // NR22 FF17
                    sq2_envsgn_old <= sq2_envsgn;
                    sq2_envper_old <= sq2_envper;
                    sq2_svol <= s1_writedata[7:4];
                    sq2_nr2change <= 1'b1;
                    sq2_envsgn <= s1_writedata[3];
                    sq2_envper <= s1_writedata[2:0];
                end
                7'b0011000: begin // NR23 FF18
                    sq2_freq[7:0] <= s1_writedata;
                end
                7'b0011001: begin // NR24 FF19
                    sq2_trigger <= s1_writedata[7];
                    if (s1_writedata[7]) begin
                        if (sq2_playing)
                            sq2_trigger_cnt <= 3'd2;
                        else
                            sq2_trigger_cnt <= 3'd4;
                    end
                    if (!sq2_lenchk && s1_writedata[6] && en_len_r)
                        sq2_lenquirk <= 1'b1;
                    sq2_lenchk <= s1_writedata[6];
                    sq2_freq[10:8] <= s1_writedata[2:0];
                end

                // Wave
                7'b0011010: begin // NR30 FF1A
                    wav_enable <= s1_writedata[7];
                end
                7'b0011011: begin // NR31 FF1B
                    wav_slen <= 9'd256 - {1'b0, s1_writedata};
                    wav_lenchange <= 1'b1;
                end
                7'b0011100: begin // NR32 FF1C
                    wav_volsh <= s1_writedata[6:5];
                end
                7'b0011101: begin // NR33 FF1D
                    wav_freq[7:0] <= s1_writedata;
                end
                7'b0011110: begin // NR34 FF1E
                    wav_trigger <= s1_writedata[7];
                    if (s1_writedata[7])
                        wav_trigger_cnt <= 2'd2;
                    if (!wav_lenchk && s1_writedata[6] && en_len_r)
                        wav_lenquirk <= 1'b1;
                    wav_lenchk <= s1_writedata[6];
                    wav_freq[10:8] <= s1_writedata[2:0];
                end

                // Noise
                7'b0100000: begin // NR41 FF20
                    noi_slen <= 7'd64 - {1'b0, s1_writedata[5:0]};
                    noi_lenchange <= 1'b1;
                end
                7'b0100001: begin // NR42 FF21
                    noi_envsgn_old <= noi_envsgn;
                    noi_envper_old <= noi_envper;
                    noi_svol <= s1_writedata[7:4];
                    noi_nr2change <= 1'b1;
                    noi_envsgn <= s1_writedata[3];
                    noi_envper <= s1_writedata[2:0];
                end
                7'b0100010: begin // NR43 FF22
                    noi_freqsh <= s1_writedata[7:4];
                    noi_short <= s1_writedata[3];
                    noi_div <= s1_writedata[2:0];
                    noi_freqchange <= 1'b1;
                end
                7'b0100011: begin // NR44 FF23
                    noi_trigger <= s1_writedata[7];
                    if (s1_writedata[7]) begin
                        if (!noi_playing)
                            noi_trigger_cnt <= 3'd2;
                        else
                            noi_trigger_cnt <= 3'd4;
                    end
                    if (!noi_lenchk && s1_writedata[6] && en_len_r)
                        noi_lenquirk <= 1'b1;
                    noi_lenchk <= s1_writedata[6];
                end

                // Control/Status
                7'b0100100: ch_vol <= s1_writedata; // NR50 FF24
                7'b0100101: ch_map <= s1_writedata; // NR51 FF25
                7'b0100110: begin // NR52 FF26
                    snd_enable <= s1_writedata[7];
                    if (!s1_writedata[7]) begin
                        // Reset all registers when APU disabled
                        sq1_swper <= 3'd0;
                        sq1_swdir <= 1'b0;
                        sq1_swshift <= 3'd0;
                        sq1_duty <= 2'd0;
                        sq1_svol <= 4'd0;
                        sq1_envsgn <= 1'b0;
                        sq1_envper <= 3'd0;
                        sq1_freq <= 11'd0;
                        sq1_lenchk <= 1'b0;
                        sq1_trigger <= 1'b0;

                        sq2_duty <= 2'd0;
                        sq2_svol <= 4'd0;
                        sq2_envsgn <= 1'b0;
                        sq2_envper <= 3'd0;
                        sq2_freq <= 11'd0;
                        sq2_lenchk <= 1'b0;
                        sq2_trigger <= 1'b0;

                        wav_enable <= 1'b0;
                        wav_volsh <= 2'd0;
                        wav_freq <= 11'd0;
                        wav_trigger <= 1'b0;
                        wav_lenchk <= 1'b0;

                        noi_svol <= 4'd0;
                        noi_envsgn <= 1'b0;
                        noi_envper <= 3'd0;
                        noi_freqsh <= 4'd0;
                        noi_short <= 1'b0;
                        noi_div <= 3'd0;
                        noi_trigger <= 1'b0;
                        noi_lenchk <= 1'b0;

                        ch_map <= 8'd0;
                        ch_vol <= 8'd0;

                        sq1_trigger_cnt <= 3'd0;
                        sq2_trigger_cnt <= 3'd0;
                        wav_trigger_cnt <= 2'd0;
                        noi_trigger_cnt <= 3'd0;

                        if (is_gbc) begin
                            sq1_slen <= 7'd0;
                            sq2_slen <= 7'd0;
                            wav_slen <= 9'd0;
                            noi_slen <= 7'd0;
                        end
                    end
                end

                // Wave Table (FF30-FF3F)
                7'b0110000, 7'b0110001, 7'b0110010, 7'b0110011,
                7'b0110100, 7'b0110101, 7'b0110110, 7'b0110111,
                7'b0111000, 7'b0111001, 7'b0111010, 7'b0111011,
                7'b0111100, 7'b0111101, 7'b0111110, 7'b0111111: begin
                    reg [3:0] wave_index_write;
                    reg [4:0] wave_index_lo;
                    if (wav_playing)
                        wave_index_write = wav_index[4:1];
                    else
                        wave_index_write = s1_addr[3:0];

                    if (is_gbc || wav_access > 0 || !wav_playing) begin
                        wave_index_lo = {wave_index_write, 1'b0};
                        wav_ram[wave_index_lo] <= s1_writedata[7:4];
                        wav_ram[wave_index_lo + 1] <= s1_writedata[3:0];
                    end
                end

                default: ;
            endcase
        end
    end
end

// Register read process (combinational)
always @(*) begin
    reg [3:0] wave_index_read;
    reg [4:0] wave_index_lo;

    // Initialize to avoid latch warnings
    wave_index_read = 4'd0;
    wave_index_lo = 5'd0;

    case (s1_addr)
        // Square 1
        7'b0010000: s1_readdata = {1'b1, sq1_swper, sq1_swdir, sq1_swshift}; // NR10
        7'b0010001: s1_readdata = {sq1_duty, 6'b111111}; // NR11
        7'b0010010: s1_readdata = {sq1_svol, sq1_envsgn, sq1_envper}; // NR12
        7'b0010011: s1_readdata = 8'hFF; // NR13
        7'b0010100: s1_readdata = {1'b1, sq1_lenchk, 6'b111111}; // NR14

        // Square 2
        7'b0010110: s1_readdata = {sq2_duty, 6'b111111}; // NR21
        7'b0010111: s1_readdata = {sq2_svol, sq2_envsgn, sq2_envper}; // NR22
        7'b0011000: s1_readdata = 8'hFF; // NR23
        7'b0011001: s1_readdata = {1'b1, sq2_lenchk, 6'b111111}; // NR24

        // Wave
        7'b0011010: s1_readdata = {wav_enable, 7'b1111111}; // NR30
        7'b0011011: s1_readdata = 8'hFF; // NR31
        7'b0011100: s1_readdata = {1'b1, wav_volsh, 5'b11111}; // NR32
        7'b0011101: s1_readdata = 8'hFF; // NR33
        7'b0011110: s1_readdata = {1'b1, wav_lenchk, 6'b111111}; // NR34

        // Noise
        7'b0100000: s1_readdata = 8'hFF; // NR41
        7'b0100001: s1_readdata = {noi_svol, noi_envsgn, noi_envper}; // NR42
        7'b0100010: s1_readdata = {noi_freqsh, noi_short, noi_div}; // NR43
        7'b0100011: s1_readdata = {1'b1, noi_lenchk, 6'b111111}; // NR44

        // Control/Status
        7'b0100100: s1_readdata = ch_vol; // NR50
        7'b0100101: s1_readdata = ch_map; // NR51
        7'b0100110: s1_readdata = {snd_enable, 3'b111, noi_playing, wav_playing, sq2_playing, sq1_playing}; // NR52

        // Undocumented PCM registers
        7'b1110110: begin // PCM12 FF76
            if (is_gbc) begin
                s1_readdata = 8'd0;
                if (sq2_playing) s1_readdata[7:4] = sq2_wav;
                if (sq1_playing) s1_readdata[3:0] = sq1_wav;
            end else begin
                s1_readdata = 8'hFF;
            end
        end
        7'b1110111: begin // PCM34 FF77
            if (is_gbc) begin
                s1_readdata = 8'd0;
                if (noi_playing) s1_readdata[7:4] = noi_wav;
                if (wav_playing) s1_readdata[3:0] = wav_wav;
            end else begin
                s1_readdata = 8'hFF;
            end
        end

        // Wave Table (FF30-FF3F)
        7'b0110000, 7'b0110001, 7'b0110010, 7'b0110011,
        7'b0110100, 7'b0110101, 7'b0110110, 7'b0110111,
        7'b0111000, 7'b0111001, 7'b0111010, 7'b0111011,
        7'b0111100, 7'b0111101, 7'b0111110, 7'b0111111: begin
            if (wav_playing)
                wave_index_read = wav_index[4:1];
            else
                wave_index_read = s1_addr[3:0];

            if (is_gbc || wav_access > 0 || !wav_playing) begin
                wave_index_lo = {wave_index_read, 1'b0};
                s1_readdata = {wav_ram[wave_index_lo], wav_ram[wave_index_lo + 1]};
            end else begin
                s1_readdata = 8'hFF;
            end
        end

        default: s1_readdata = 8'hFF;
    endcase
end

// Square 1 channel
// Duty cycle patterns
wire [7:0] duty_0 = 8'b00000001;
wire [7:0] duty_1 = 8'b10000001;
wire [7:0] duty_2 = 8'b10000111;
wire [7:0] duty_3 = 8'b01111110;

reg [10:0] sq1_fcnt;
reg [2:0]  sq1_phase;
reg [6:0]  sq1_len;
reg [3:0]  sq1_envcnt;
reg [3:0]  sq1_swcnt;
reg [11:0] sq1_swoffs;
reg [11:0] sq1_swfr;
reg        sq1_sweep_en;
reg        sweep_calculate;
reg        sweep_update;
reg        sweep_negate;
reg [1:0]  sq1_sduty;
reg [10:0] sq1_trigger_freq;

// Square 1 DAC enable
always @(*) begin
    sq1_dac_en = 1'b1;
    if ({sq1_svol, sq1_envsgn} == 5'b00000)
        sq1_dac_en = 1'b0;
end

// Square 1 waveform output
always @(*) begin
    if (sq1_out && !sq1_suppressed)
        sq1_wav = sq1_vol;
    else
        sq1_wav = 4'd0;
end

always @(posedge clk) begin
    reg [11:0] acc_fcnt;
    reg [7:0] tmp_volume;

    if (reset) begin
        sq1_playing <= 1'b0;
        sq1_fr2 <= 11'd0;
        sq1_fcnt <= 11'd0;
        sq1_phase <= 3'd0;
        sq1_vol <= 4'd0;
        sq1_envcnt <= 4'd0;
        sq1_swcnt <= 4'd0;
        sq1_swoffs <= 12'd0;
        sq1_swfr <= 12'd0;
        sq1_out <= 1'b0;
        sq1_suppressed <= 1'b1;
        sq1_sduty <= 2'd0;
        sweep_calculate <= 1'b0;
        sweep_update <= 1'b0;
        sq1_sweep_en <= 1'b0;
        sweep_negate <= 1'b0;
        sq1_len <= 7'd0;
        sq1_trigger_r <= 1'b0;
        sq1_trigger_freq <= 11'd0;
    end else if (ce) begin
        if (sq1_lenchange)
            sq1_len <= sq1_slen;

        sq1_trigger_r <= sq1_trigger;

        if (snd_enable) begin
            if (en_snd4) begin
                // Frequency timer
                if (sq1_playing) begin
                    acc_fcnt = {1'b0, sq1_fcnt} + 1;
                    if (acc_fcnt[11]) begin
                        sq1_suppressed <= 1'b0;
                        if (sq1_phase < 7)
                            sq1_phase <= sq1_phase + 1;
                        else
                            sq1_phase <= 0;
                        sq1_fcnt <= sq1_freq;
                        sq1_sduty <= sq1_duty;
                    end else begin
                        sq1_fcnt <= acc_fcnt[10:0];
                    end
                end

                // Duty cycle output
                case (sq1_sduty)
                    2'b00: sq1_out <= duty_0[sq1_phase];
                    2'b01: sq1_out <= duty_1[sq1_phase];
                    2'b10: sq1_out <= duty_2[sq1_phase];
                    2'b11: sq1_out <= duty_3[sq1_phase];
                endcase
            end

            // Length counter
            if (en_len || sq1_lenquirk) begin
                if (sq1_len > 0 && sq1_lenchk)
                    sq1_len <= sq1_len - 1;
            end

            // Sweep processing
            if (en_sweep) begin
                sq1_swcnt <= sq1_swcnt - 1;
                if (sq1_swcnt == 0) begin
                    if (sq1_swper == 3'd0)
                        sq1_swcnt <= 4'd8;
                    else
                        sq1_swcnt <= {1'b0, sq1_swper};

                    if (sq1_sweep_en && sq1_swper != 3'd0) begin
                        sweep_calculate <= 1'b1;
                        sweep_update <= 1'b1;
                    end
                end
            end

            sq1_freqchange <= 1'b0;

            if (sq1_sweep_en) begin
                // Calculate next sweep frequency
                if (sweep_calculate) begin
                    case (sq1_swshift)
                        3'd0: sq1_swoffs <= {1'b0, sq1_fr2};
                        3'd1: sq1_swoffs <= {2'b00, sq1_fr2[10:1]};
                        3'd2: sq1_swoffs <= {3'b000, sq1_fr2[10:2]};
                        3'd3: sq1_swoffs <= {4'b0000, sq1_fr2[10:3]};
                        3'd4: sq1_swoffs <= {5'b00000, sq1_fr2[10:4]};
                        3'd5: sq1_swoffs <= {6'b000000, sq1_fr2[10:5]};
                        3'd6: sq1_swoffs <= {7'b0000000, sq1_fr2[10:6]};
                        3'd7: sq1_swoffs <= {8'b00000000, sq1_fr2[10:7]};
                    endcase
                    if (sq1_swdir) begin
                        sq1_swfr <= {1'b0, sq1_fr2} - sq1_swoffs;
                        sweep_negate <= 1'b1;
                    end else begin
                        sq1_swfr <= {1'b0, sq1_fr2} + sq1_swoffs;
                        sweep_negate <= 1'b0;
                    end
                    sweep_calculate <= 1'b0;
                end

                // Update registers
                if (sweep_update) begin
                    sweep_update <= 1'b0;
                    if (sq1_swper != 3'd0 && sq1_swshift != 3'd0) begin
                        sq1_fr2 <= sq1_swfr[10:0];
                        sq1_freqchange <= 1'b1;
                        sweep_calculate <= 1'b1;
                    end
                end
            end

            if (sq1_playing) begin
                // Envelope counter
                if (en_env && sq1_envper != 3'd0) begin
                    sq1_envcnt <= sq1_envcnt - 1;
                    if (sq1_envcnt == 0) begin
                        if (sq1_envsgn) begin
                            if (sq1_vol != 4'hF)
                                sq1_vol <= sq1_vol + 1;
                        end else begin
                            if (sq1_vol != 4'h0)
                                sq1_vol <= sq1_vol - 1;
                        end
                        if (sq1_envper == 3'd0)
                            sq1_envcnt <= 4'd8;
                        else
                            sq1_envcnt <= {1'b0, sq1_envper};
                    end
                end

                // Check end conditions
                if ((sq1_lenchk && sq1_len == 0) ||
                    (sq1_sweep_en && sq1_swfr[11]) ||
                    (sq1_sweep_en && sq1_swdir_change && sweep_negate)) begin
                    sq1_playing <= 1'b0;
                    sq1_envcnt <= 4'd0;
                    sq1_swcnt <= 4'd0;
                    sq1_swfr <= 12'd0;
                    sq1_sweep_en <= 1'b0;
                end
            end

            // Zombie mode
            if (((sq1_trigger_r && !sq1_trigger) || sq1_nr2change) && sq1_playing) begin
                tmp_volume = {4'd0, sq1_vol};
                if (sq1_envsgn)
                    tmp_volume = tmp_volume + 1;
                if (sq1_envsgn ^ sq1_envsgn_old)
                    tmp_volume = 8'h10 - tmp_volume;
                if (sq1_envper != 3'd0 && sq1_envper_old == 3'd0 && tmp_volume != 8'd0 && !sq1_envsgn)
                    tmp_volume = tmp_volume - 1;
                if (sq1_envper_old != 3'd0 && sq1_envsgn)
                    tmp_volume = tmp_volume - 1;
                sq1_vol <= tmp_volume[3:0];

                if (sq1_svol == 4'd0 && !sq1_envsgn)
                    sq1_playing <= 1'b0;
            end

            // Reset frequency counter if already playing
            if (sq1_trigger && sq1_playing)
                sq1_fcnt <= 11'd0;

            // Rising edge of trigger
            if (!sq1_trigger_r && sq1_trigger)
                sq1_trigger_freq <= sq1_freq;

            // Falling edge of trigger - start playing
            if (sq1_trigger_r && !sq1_trigger) begin
                if (!sq1_playing)
                    sq1_suppressed <= 1'b1;

                sq1_vol <= sq1_svol;
                sq1_fr2 <= sq1_freq;
                sq1_sweep_en <= 1'b0;
                if (sq1_swper != 3'd0 || sq1_swshift != 3'd0)
                    sq1_sweep_en <= 1'b1;

                if (sq1_swshift != 3'd0)
                    sweep_calculate <= 1'b1;

                if (sq1_swper == 3'd0)
                    sq1_swcnt <= 4'd8;
                else
                    sq1_swcnt <= {1'b0, sq1_swper};
                sweep_negate <= 1'b0;

                sq1_fcnt <= sq1_trigger_freq;

                if (!(sq1_svol == 4'd0 && !sq1_envsgn))
                    sq1_playing <= 1'b1;

                if (sq1_envper == 3'd0)
                    sq1_envcnt <= 4'd8;
                else
                    sq1_envcnt <= {1'b0, sq1_envper};

                if (sq1_len == 0) begin
                    if (sq1_lenchk && en_len_r)
                        sq1_len <= 7'd63;
                    else
                        sq1_len <= 7'd64;
                end
            end
        end else begin
            // Sound disabled
            sq1_playing <= 1'b0;
            sq1_fr2 <= 11'd0;
            sq1_fcnt <= 11'd0;
            sq1_phase <= 3'd0;
            sq1_vol <= 4'd0;
            sq1_envcnt <= 4'd0;
            sq1_swcnt <= 4'd0;
            sq1_swoffs <= 12'd0;
            sq1_swfr <= 12'd0;
            sq1_out <= 1'b0;
            sq1_suppressed <= 1'b1;
            sq1_sduty <= 2'd0;
            sweep_calculate <= 1'b0;
            sweep_update <= 1'b0;
            sq1_sweep_en <= 1'b0;
            sweep_negate <= 1'b0;
            if (is_gbc)
                sq1_len <= 7'd0;
            sq1_trigger_r <= 1'b0;
        end
    end
end

// Square 2 channel (similar to Square 1 but without sweep)
reg [10:0] sq2_fcnt;
reg [2:0]  sq2_phase;
reg [6:0]  sq2_len;
reg [3:0]  sq2_envcnt;
reg [1:0]  sq2_sduty;
reg [10:0] sq2_trigger_freq;

// Square 2 DAC enable
always @(*) begin
    sq2_dac_en = 1'b1;
    if ({sq2_svol, sq2_envsgn} == 5'b00000)
        sq2_dac_en = 1'b0;
end

// Square 2 waveform output
always @(*) begin
    if (sq2_out && !sq2_suppressed)
        sq2_wav = sq2_vol;
    else
        sq2_wav = 4'd0;
end

always @(posedge clk) begin
    reg [11:0] acc_fcnt;
    reg [7:0] tmp_volume;

    if (reset) begin
        sq2_playing <= 1'b0;
        sq2_fcnt <= 11'd0;
        sq2_phase <= 3'd0;
        sq2_vol <= 4'd0;
        sq2_envcnt <= 4'd0;
        sq2_out <= 1'b0;
        sq2_suppressed <= 1'b1;
        sq2_sduty <= 2'd0;
        sq2_len <= 7'd0;
        sq2_trigger_r <= 1'b0;
        sq2_trigger_freq <= 11'd0;
    end else if (ce) begin
        if (sq2_lenchange)
            sq2_len <= sq2_slen;

        sq2_trigger_r <= sq2_trigger;

        if (snd_enable) begin
            if (en_snd4) begin
                if (sq2_playing) begin
                    acc_fcnt = {1'b0, sq2_fcnt} + 1;
                    if (acc_fcnt[11]) begin
                        sq2_suppressed <= 1'b0;
                        if (sq2_phase < 7)
                            sq2_phase <= sq2_phase + 1;
                        else
                            sq2_phase <= 0;
                        sq2_fcnt <= sq2_freq;
                        sq2_sduty <= sq2_duty;
                    end else begin
                        sq2_fcnt <= acc_fcnt[10:0];
                    end
                end

                case (sq2_sduty)
                    2'b00: sq2_out <= duty_0[sq2_phase];
                    2'b01: sq2_out <= duty_1[sq2_phase];
                    2'b10: sq2_out <= duty_2[sq2_phase];
                    2'b11: sq2_out <= duty_3[sq2_phase];
                endcase
            end

            // Length counter
            if (en_len || sq2_lenquirk) begin
                if (sq2_len > 0 && sq2_lenchk)
                    sq2_len <= sq2_len - 1;
            end

            if (sq2_playing) begin
                // Envelope counter
                if (en_env && sq2_envper != 3'd0) begin
                    sq2_envcnt <= sq2_envcnt - 1;
                    if (sq2_envcnt == 0) begin
                        if (sq2_envsgn) begin
                            if (sq2_vol != 4'hF)
                                sq2_vol <= sq2_vol + 1;
                        end else begin
                            if (sq2_vol != 4'h0)
                                sq2_vol <= sq2_vol - 1;
                        end
                        if (sq2_envper == 3'd0)
                            sq2_envcnt <= 4'd8;
                        else
                            sq2_envcnt <= {1'b0, sq2_envper};
                    end
                end

                // Check end conditions
                if (sq2_lenchk && sq2_len == 0) begin
                    sq2_playing <= 1'b0;
                    sq2_envcnt <= 4'd0;
                end
            end

            // Zombie mode
            if (((sq2_trigger_r && !sq2_trigger) || sq2_nr2change) && sq2_playing) begin
                tmp_volume = {4'd0, sq2_vol};
                if (sq2_envsgn)
                    tmp_volume = tmp_volume + 1;
                if (sq2_envsgn ^ sq2_envsgn_old)
                    tmp_volume = 8'h10 - tmp_volume;
                if (sq2_envper != 3'd0 && sq2_envper_old == 3'd0 && tmp_volume != 8'd0 && !sq2_envsgn)
                    tmp_volume = tmp_volume - 1;
                if (sq2_envper_old != 3'd0 && sq2_envsgn)
                    tmp_volume = tmp_volume - 1;
                sq2_vol <= tmp_volume[3:0];

                if (sq2_svol == 4'd0 && !sq2_envsgn)
                    sq2_playing <= 1'b0;
            end

            // Reset frequency counter if already playing
            if (sq2_trigger && sq2_playing)
                sq2_fcnt <= 11'd0;

            // Rising edge of trigger
            if (!sq2_trigger_r && sq2_trigger)
                sq2_trigger_freq <= sq2_freq;

            // Falling edge of trigger
            if (sq2_trigger_r && !sq2_trigger) begin
                if (!sq2_playing)
                    sq2_suppressed <= 1'b1;

                sq2_vol <= sq2_svol;
                sq2_fcnt <= sq2_trigger_freq;

                if (!(sq2_svol == 4'd0 && !sq2_envsgn))
                    sq2_playing <= 1'b1;

                if (sq2_envper == 3'd0)
                    sq2_envcnt <= 4'd8;
                else
                    sq2_envcnt <= {1'b0, sq2_envper};

                if (sq2_len == 0) begin
                    if (sq2_lenchk && en_len_r)
                        sq2_len <= 7'd63;
                    else
                        sq2_len <= 7'd64;
                end
            end
        end else begin
            sq2_playing <= 1'b0;
            sq2_fcnt <= 11'd0;
            sq2_phase <= 3'd0;
            sq2_vol <= 4'd0;
            sq2_envcnt <= 4'd0;
            sq2_out <= 1'b0;
            sq2_suppressed <= 1'b1;
            sq2_sduty <= 2'd0;
            if (is_gbc)
                sq2_len <= 7'd0;
            sq2_trigger_r <= 1'b0;
        end
    end
end

// Wave channel
reg [10:0] wav_fcnt;
reg [8:0]  wav_len;
reg        wav_shift_r;
reg [10:0] wav_trigger_freq;

// Wave waveform output
always @(*) begin
    if (!wav_playing)
        wav_wav = 4'd0;
    else begin
        case (wav_volsh)
            2'b01: wav_wav = wav_wav_r;
            2'b10: wav_wav = {1'b0, wav_wav_r[3:1]};
            2'b11: wav_wav = {2'b00, wav_wav_r[3:2]};
            default: wav_wav = 4'd0;
        endcase
    end
end

always @(posedge clk) begin
    reg [11:0] acc_fcnt;
    reg wav_shift;

    if (reset) begin
        wav_wav_r <= 4'd0;
        wav_playing <= 1'b0;
        wav_fcnt <= 11'd0;
        wav_shift_r <= 1'b0;
        wav_index <= 5'd0;
        wav_access <= 2'd0;
        wav_len <= 9'd0;
        wav_trigger_r <= 1'b0;
        wav_trigger_freq <= 11'd0;
    end else if (ce) begin
        if (wav_lenchange)
            wav_len <= wav_slen;

        wav_trigger_r <= wav_trigger;

        if (snd_enable) begin
            if (wav_access > 0)
                wav_access <= wav_access - 1;

            wav_shift = 1'b0;

            if (en_snd2) begin
                if (wav_playing) begin
                    acc_fcnt = {1'b0, wav_fcnt} + 1;
                    if (acc_fcnt[11]) begin
                        wav_shift = 1'b1;
                        wav_fcnt <= wav_freq;
                    end else begin
                        wav_fcnt <= acc_fcnt[10:0];
                    end
                end
            end

            if (wav_trigger_r && !wav_trigger) begin
                wav_index <= 5'd0;
                wav_shift_r <= 1'b0;
            end else begin
                if (wav_shift && !wav_shift_r) begin
                    wav_index <= wav_index + 1;
                    wav_wav_r <= wav_ram[wav_index + 1];
                    wav_access <= 2'd2;
                end
                wav_shift_r <= wav_shift;
            end

            // Length counter
            if (en_len || wav_lenquirk) begin
                if (wav_len > 0 && wav_lenchk)
                    wav_len <= wav_len - 1;
            end

            if (wav_playing) begin
                if ((wav_lenchk && wav_len == 0) || !wav_enable)
                    wav_playing <= 1'b0;
            end

            // Rising edge of trigger
            if (!wav_trigger_r && wav_trigger)
                wav_trigger_freq <= wav_freq;

            // Falling edge of trigger
            if (wav_trigger_r && !wav_trigger) begin
                wav_fcnt <= wav_trigger_freq;
                wav_playing <= 1'b1;
                if (wav_len == 0) begin
                    if (wav_lenchk && en_len_r)
                        wav_len <= 9'd255;
                    else
                        wav_len <= 9'd256;
                end
            end
        end else begin
            wav_wav_r <= 4'd0;
            wav_playing <= 1'b0;
            wav_fcnt <= 11'd0;
            wav_shift_r <= 1'b0;
            wav_index <= 5'd0;
            wav_access <= 2'd0;
            if (is_gbc)
                wav_len <= 9'd0;
            wav_trigger_r <= 1'b0;
        end
    end
end

// Noise channel
reg [19:0] noi_period;
reg [19:0] noi_fcnt;
reg [14:0] noi_lfsr;
reg [6:0]  noi_len;
reg [2:0]  noi_envcnt;
reg        noi_out;

// Noise DAC enable
always @(*) begin
    noi_dac_en = 1'b1;
    if ({noi_svol, noi_envsgn} == 5'b00000)
        noi_dac_en = 1'b0;
end

// Noise waveform output
always @(*) begin
    if (noi_out)
        noi_wav = noi_vol;
    else
        noi_wav = 4'd0;
end

always @(posedge clk) begin
    reg noi_xor;
    reg [7:0] tmp_volume;

    if (reset) begin
        noi_playing <= 1'b0;
        noi_fcnt <= 20'd0;
        noi_lfsr <= 15'd0;
        noi_vol <= 4'd0;
        noi_envcnt <= 3'd0;
        noi_out <= 1'b0;
        noi_len <= 7'd0;
        noi_trigger_r <= 1'b0;
        noi_period <= 20'd0;
    end else if (ce) begin
        if (noi_lenchange)
            noi_len <= noi_slen;

        noi_trigger_r <= noi_trigger;

        if (!snd_enable) begin
            noi_playing <= 1'b0;
            noi_fcnt <= 20'd0;
            noi_lfsr <= 15'd0;
            noi_vol <= 4'd0;
            noi_envcnt <= 3'd0;
            noi_out <= 1'b0;
            if (is_gbc)
                noi_len <= 7'd0;
            noi_trigger_r <= 1'b0;
        end else begin
            // LFSR
            if (noi_playing && en_snd4) begin
                if (noi_fcnt == 1) begin
                    noi_xor = ~(noi_lfsr[0] ^ noi_lfsr[1]);
                    noi_lfsr <= {noi_xor, noi_lfsr[14:1]};
                    if (noi_short)
                        noi_lfsr[6] <= noi_xor;
                    noi_out <= noi_lfsr[0];
                    noi_fcnt <= noi_period;
                end else begin
                    noi_fcnt <= noi_fcnt - 1;
                end
            end

            // Length counter
            if ((en_len || noi_lenquirk) && noi_lenchk) begin
                if (noi_len > 0)
                    noi_len <= noi_len - 1;
            end

            // Check end conditions
            if (noi_lenchk && noi_len == 0)
                noi_playing <= 1'b0;

            // Envelope counter
            if (noi_playing && en_env && noi_envper != 3'd0) begin
                noi_envcnt <= noi_envcnt - 1;
                if (noi_envcnt == 0) begin
                    if (noi_envsgn) begin
                        if (noi_vol != 4'hF)
                            noi_vol <= noi_vol + 1;
                    end else begin
                        if (noi_vol != 4'h0)
                            noi_vol <= noi_vol - 1;
                    end
                    noi_envcnt <= noi_envper;
                end
            end

            // Zombie mode
            if (((!noi_trigger && noi_trigger_r) || noi_nr2change) && noi_playing) begin
                tmp_volume = {4'd0, noi_vol};
                if (noi_envsgn)
                    tmp_volume = tmp_volume + 1;
                if (noi_envsgn ^ noi_envsgn_old)
                    tmp_volume = 8'h10 - tmp_volume;
                if (noi_envper != 3'd0 && noi_envper_old == 3'd0 && tmp_volume != 8'd0 && !noi_envsgn)
                    tmp_volume = tmp_volume - 1;
                if (noi_envper_old != 3'd0 && noi_envsgn)
                    tmp_volume = tmp_volume - 1;
                noi_vol <= tmp_volume[3:0];
            end

            // Calculate noise period
            if (noi_trigger || noi_freqchange) begin
                noi_period <= 20'd0;
                if (noi_div == 3'd0)
                    noi_period <= 20'd2 << noi_freqsh;
                else
                    noi_period <= {15'd0, noi_div, 2'd0} << noi_freqsh;
                noi_fcnt <= noi_period;
            end

            // Falling edge of trigger
            if (noi_trigger_r && !noi_trigger) begin
                noi_playing <= 1'b1;
                noi_vol <= noi_svol;
                noi_lfsr <= 15'd0;
                noi_envcnt <= noi_envper;

                if (noi_len == 0) begin
                    if (noi_lenchk && en_len_r)
                        noi_len <= 7'd63;
                    else
                        noi_len <= 7'd64;
                end
            end

            // DAC disabled check
            if ({noi_svol, noi_envsgn} == 5'b00000)
                noi_playing <= 1'b0;
        end
    end
end

// Instantiate DACs
apu_dac sq1_dac_inst (
    .clk(clk),
    .ce(ce),
    .dac_en(sq1_dac_en),
    .dac_invert(~remove_pops),
    .dac_input(sq1_wav),
    .dac_output(sq1_dac_out)
);

apu_dac sq2_dac_inst (
    .clk(clk),
    .ce(ce),
    .dac_en(sq2_dac_en),
    .dac_invert(~remove_pops),
    .dac_input(sq2_wav),
    .dac_output(sq2_dac_out)
);

apu_dac wav_dac_inst (
    .clk(clk),
    .ce(ce),
    .dac_en(wav_enable),
    .dac_invert(~remove_pops),
    .dac_input(wav_wav),
    .dac_output(wav_dac_out)
);

apu_dac noi_dac_inst (
    .clk(clk),
    .ce(ce),
    .dac_en(noi_dac_en),
    .dac_invert(~remove_pops),
    .dac_input(noi_wav),
    .dac_output(noi_dac_out)
);

// Mixer
always @(*) begin
    reg signed [10:0] snd_left_in;
    reg signed [10:0] snd_right_in;
    reg signed [15:0] snd_tmp;
    reg signed [8:0] wav_analog;
    integer k;

    snd_left_in = 11'sd0;
    snd_right_in = 11'sd0;

    for (k = 0; k < 4; k = k + 1) begin
        case (k)
            0: wav_analog = sq1_dac_out;
            1: wav_analog = sq2_dac_out;
            2: wav_analog = wav_dac_out;
            3: wav_analog = noi_dac_out;
            default: wav_analog = 9'sd0;
        endcase

        if (ch_map[k])
            snd_right_in = snd_right_in + wav_analog;

        if (ch_map[k + 4])
            snd_left_in = snd_left_in + wav_analog;
    end

    snd_tmp = snd_right_in * $signed({2'b00, ch_vol[2:0]} + 1);
    if (remove_pops)
        snd_right = snd_tmp <<< 1;
    else
        snd_right = snd_tmp;

    snd_tmp = snd_left_in * $signed({2'b00, ch_vol[6:4]} + 1);
    if (remove_pops)
        snd_left = snd_tmp <<< 1;
    else
        snd_left = snd_tmp;
end

endmodule

//
// APU DAC module - converts 4-bit digital to pseudo-analog with decay
//
module apu_dac (
    input         clk,
    input         ce,
    input         dac_en,
    input         dac_invert,
    input  [3:0]  dac_input,
    output signed [8:0] dac_output
);

// Analog value has range [-256, 255], decays to zero when DAC disabled
// Decay rate: ~6ms from max to zero (based on SameBoy)
parameter DAC_DECAY_PERIOD = 100;

reg [6:0] dac_decay_timer;
reg signed [8:0] dac_analog;

assign dac_output = dac_analog;

// DAC output function
function signed [8:0] dac_out;
    input [3:0] wav;
    input invert;
begin
    if (invert)
        dac_out = $signed({(wav ^ 4'b0111), 5'b00000}); // 0xF = -256, 0x0 = 224
    else
        dac_out = $signed({1'b0, wav, 4'b0000}); // 0xF = 240, 0x0 = 0
end
endfunction

// Decay timer
always @(posedge clk) begin
    if (ce) begin
        if (dac_en) begin
            dac_decay_timer <= DAC_DECAY_PERIOD;
        end else begin
            if (dac_decay_timer > 0)
                dac_decay_timer <= dac_decay_timer - 1;
            else
                dac_decay_timer <= DAC_DECAY_PERIOD;
        end
    end
end

// DAC analog output with decay
always @(posedge clk) begin
    if (ce) begin
        if (dac_en) begin
            dac_analog <= dac_out(dac_input, dac_invert);
        end else if (dac_decay_timer == 0) begin
            if (dac_analog < 0)
                dac_analog <= dac_analog + 1;
            else if (dac_analog > 0)
                dac_analog <= dac_analog - 1;
        end
    end
end

endmodule
