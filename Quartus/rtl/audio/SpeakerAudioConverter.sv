//============================================================================
//
//  SpeakerAudioConverter - PC Speaker to Audio Sample Converter
//  Converts 1-bit PC speaker signal to 16-bit signed PCM audio samples
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//  This program is free software; you can redistribute it and/or modify it
//  under the terms of the GNU General Public License as published by the Free
//  Software Foundation; either version 3 of the License, or (at your option)
//  any later version.
//
//============================================================================

`default_nettype none

module SpeakerAudioConverter (
    input  logic        clk_sys,          // System clock (50 MHz)
    input  logic        clk_audio,        // Audio clock (24.576 MHz)
    input  logic        reset,            // Synchronous reset

    input  logic        speaker_in,       // 1-bit speaker signal (from timer & gate logic)
    input  logic [1:0]  volume,           // Volume control: 0=quiet, 3=loud

    output logic [15:0] audio_out_l,      // 16-bit signed PCM left channel
    output logic [15:0] audio_out_r       // 16-bit signed PCM right channel
);

// Volume level mapping (signed 16-bit values)
// Volume 0: ±2048  (1/8 scale, -42 dB)
// Volume 1: ±4096  (1/4 scale, -36 dB)
// Volume 2: ±8192  (1/2 scale, -30 dB)
// Volume 3: ±16383 (near full scale, -24 dB)

// Clock domain crossing: sys_clk -> clk_audio
logic speaker_sync;

// Two-stage synchronizer for clock domain crossing
logic speaker_meta;
always_ff @(posedge clk_audio or posedge reset) begin
    if (reset) begin
        speaker_meta <= 1'b0;
        speaker_sync <= 1'b0;
    end
    else begin
        speaker_meta <= speaker_in;   // First stage (metastability catcher)
        speaker_sync <= speaker_meta;  // Second stage (stable)
    end
end

// Audio sample generation
// Generate samples at audio clock rate with volume scaling
logic [15:0] volume_level;
logic [15:0] audio_sample;

// Volume level lookup
always_comb begin
    case (volume)
        2'b00: volume_level = 16'd2048;   // 1/8 scale
        2'b01: volume_level = 16'd4096;   // 1/4 scale
        2'b10: volume_level = 16'd8192;   // 1/2 scale
        2'b11: volume_level = 16'd16383;  // Full scale
        default: volume_level = 16'd4096; // Default to 1/4
    endcase
end

// Convert 1-bit speaker to signed 16-bit PCM
// speaker = 1 -> positive voltage -> positive PCM value
// speaker = 0 -> negative voltage -> negative PCM value
always_comb begin
    if (speaker_sync)
        audio_sample = volume_level;           // Positive value
    else
        audio_sample = ~volume_level + 16'd1;  // Two's complement (negative)
end

// Register outputs for clean timing
// Mono speaker -> same signal on both channels
always_ff @(posedge clk_audio or posedge reset) begin
    if (reset) begin
        audio_out_l <= 16'd0;
        audio_out_r <= 16'd0;
    end
    else begin
        audio_out_l <= audio_sample;
        audio_out_r <= audio_sample;  // Mono -> both channels identical
    end
end

endmodule

`default_nettype wire
