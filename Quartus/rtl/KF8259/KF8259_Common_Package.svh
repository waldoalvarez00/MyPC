//
// KF8259_Common_Package
//
// Written by Kitune-san
//
`ifndef KF8259_COMMON_PACKAGE_SVH
`define KF8259_COMMON_PACKAGE_SVH

package KF8259_Common_Package;
    function logic [7:0] rotate_right (input [7:0] source, input [2:0] rotate);
        casez (rotate)
            3'b000:  rotate_right = { source[0],   source[7:1] };
            3'b001:  rotate_right = { source[1:0], source[7:2] };
            3'b010:  rotate_right = { source[2:0], source[7:3] };
            3'b011:  rotate_right = { source[3:0], source[7:4] };
            3'b100:  rotate_right = { source[4:0], source[7:5] };
            3'b101:  rotate_right = { source[5:0], source[7:6] };
            3'b110:  rotate_right = { source[6:0], source[7]   };
            3'b111:  rotate_right = source;
            default: rotate_right = source;
        endcase
    endfunction

    function logic [7:0] rotate_left (input [7:0] source, input [2:0] rotate);
        casez (rotate)
            3'b000:  rotate_left = { source[6:0], source[7]   };
            3'b001:  rotate_left = { source[5:0], source[7:6] };
            3'b010:  rotate_left = { source[4:0], source[7:5] };
            3'b011:  rotate_left = { source[3:0], source[7:4] };
            3'b100:  rotate_left = { source[2:0], source[7:3] };
            3'b101:  rotate_left = { source[1:0], source[7:2] };
            3'b110:  rotate_left = { source[0],   source[7:1] };
            3'b111:  rotate_left = source;
            default: rotate_left = source;
        endcase
    endfunction

    function logic [7:0] resolv_priority (input [7:0] request);
        if      (request[0] == 1'b1)    resolv_priority = 8'b00000001;
        else if (request[1] == 1'b1)    resolv_priority = 8'b00000010;
        else if (request[2] == 1'b1)    resolv_priority = 8'b00000100;
        else if (request[3] == 1'b1)    resolv_priority = 8'b00001000;
        else if (request[4] == 1'b1)    resolv_priority = 8'b00010000;
        else if (request[5] == 1'b1)    resolv_priority = 8'b00100000;
        else if (request[6] == 1'b1)    resolv_priority = 8'b01000000;
        else if (request[7] == 1'b1)    resolv_priority = 8'b10000000;
        else                            resolv_priority = 8'b00000000;
    endfunction

    function logic [7:0] num2bit (input [2:0] source);
        casez (source)
            3'b000:  num2bit = 8'b00000001;
            3'b001:  num2bit = 8'b00000010;
            3'b010:  num2bit = 8'b00000100;
            3'b011:  num2bit = 8'b00001000;
            3'b100:  num2bit = 8'b00010000;
            3'b101:  num2bit = 8'b00100000;
            3'b110:  num2bit = 8'b01000000;
            3'b111:  num2bit = 8'b10000000;
            default: num2bit = 8'b00000000;
        endcase
    endfunction


/*

function automatic [2:0] bit2num(input [7:0] source);
    // Parallel comparison for the first level
    wire upper_half = |source[7:4]; // True if any bit in the upper half is set
    wire lower_half = |source[3:0]; // True if any bit in the lower half is set

    // Parallel comparison for the second level (within each half)
    wire upper_quarter = upper_half ? |source[7:6] : |source[3:2];
    wire lower_quarter = upper_half ? |source[5:4] : |source[1:0];

    // Final determination of the set bit's position
    begin
        if (upper_half) begin
            if (upper_quarter) begin
                bit2num = source[7] ? 3'b111 : 3'b110;
            end else begin
                bit2num = source[5] ? 3'b101 : 3'b100;
            end
        end else begin
            if (lower_quarter) begin
                bit2num = source[3] ? 3'b011 : 3'b010;
            end else begin
                bit2num = source[1] ? 3'b001 : 3'b000;
            end
        end
    end
endfunction


*/

    function logic [2:0] bit2num (input [7:0] source);
        if      (source[0] == 1'b1) bit2num = 3'b000;
        else if (source[1] == 1'b1) bit2num = 3'b001;
        else if (source[2] == 1'b1) bit2num = 3'b010;
        else if (source[3] == 1'b1) bit2num = 3'b011;
        else if (source[4] == 1'b1) bit2num = 3'b100;
        else if (source[5] == 1'b1) bit2num = 3'b101;
        else if (source[6] == 1'b1) bit2num = 3'b110;
        else if (source[7] == 1'b1) bit2num = 3'b111;
        else                        bit2num = 3'b111;
    endfunction

endpackage

`endif
