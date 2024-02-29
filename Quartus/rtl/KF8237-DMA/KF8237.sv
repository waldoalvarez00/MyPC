//
// KF8237
// PROGRAMMABLE DMA CONTROLLER
//
// Written by Kitune-san
//

// https://www.lo-tech.co.uk/wiki/8237_DMA_Controller

`default_nettype none

module KF8237 (

    input   wire            clock,
    input   wire            reset,
	 
    input   logic           chip_select,

    input   logic   [3:0]   address_in,

    input   logic           ready,
    input   logic           hold_acknowledge,       //  CPU granted BUS
	 
    input   logic   [3:0]   dma_request,            //  4-bit logic input vector representing 
	                                                 //  DMA request signals

    input   logic   [7:0]   data_bus_in,

    output  logic   [15:0]  address_out,
	 
	 
    output  logic   [7:0]   data_bus_out,
	 
	 
	 output  logic   [1:0]   m_bytesel,
	 
	 output  wire            bus_ack,
	 
	 
    output  logic           memory_read,
    output  logic           memory_write,

    input   logic           io_read_in,
    output  logic           io_read_n_out,
    output  logic           io_read_n_io,
	 
    input   logic           io_write_in,
    output  logic           io_write_out,
    output  logic           io_write_n_io,
	 
    input   logic           end_of_process_in,
    output  logic           end_of_process_out,
    
    
    output  logic           output_highst_address,
    output  logic           hold_request,            //  Request bus from CPU
    output  logic   [3:0]   dma_acknowledge,
    output  logic           address_enable,          //  activate the address bus
	 
	 
	 
	 // signal acts as a trigger or pulse that indicates when the address present on the address bus 
	 // should be captured or latched by the target device (e.g., memory or I/O device). 
	 // This signal helps in timing the exact moment when the address is stable and 
	 // should be read by the receiving device.
    output  logic           address_strobe

    
);

    //
    // Data Bus Buffer & Read/Write Control Logic (1)
    //
    logic           lock_bus_control;
    logic   [7:0]   internal_data_bus;
    logic           write_command_register;
    logic           write_mode_register;
    logic           write_request_register;
    logic           set_or_reset_mask_register;
    logic           write_mask_register;
    logic   [3:0]   write_base_and_current_address;
    logic   [3:0]   write_base_and_current_word_count;
    logic           clear_byte_pointer;
    logic           set_byte_pointer;
    logic           master_clear;
    logic           clear_mask_register;
    logic           read_temporary_register;
    logic           read_status_register;
    logic   [3:0]   read_current_address;
    logic   [3:0]   read_current_word_count;

    KF8237_Bus_Control_Logic u_Bus_Control_Logic (
	 
        // Bus
        .clock                              (clock),
        .reset                              (reset),
		  
		  .bus_ack                            (bus_ack),

        .chip_select                        (chip_select),
        .io_read_in                         (io_read_in),   // Request to do io read on the chip
        .io_write_in                        (io_write_in),  // Request to do io write on the chip
		  
        .address_in                         (address_in),
        .data_bus_in                        (data_bus_in),

        .lock_bus_control                   (lock_bus_control),

        // Internal Bus
        .internal_data_bus                  (internal_data_bus),
		  
        // -- write
        .write_command_register             (write_command_register),
        .write_mode_register                (write_mode_register),
        .write_request_register             (write_request_register),
        .set_or_reset_mask_register         (set_or_reset_mask_register),
        .write_mask_register                (write_mask_register),
        .write_base_and_current_address     (write_base_and_current_address),
        .write_base_and_current_word_count  (write_base_and_current_word_count),
		  
        // -- software command
        .clear_byte_pointer                 (clear_byte_pointer),
        .set_byte_pointer                   (set_byte_pointer),
        .master_clear                       (master_clear),
        .clear_mask_register                (clear_mask_register),
		  
        // -- read
        .read_temporary_register            (read_temporary_register),
        .read_status_register               (read_status_register),
        .read_current_address               (read_current_address),
        .read_current_word_count            (read_current_word_count)
    );


    //
    // Priority Encoder And Rotating Priority Logic
    //
    logic   [1:0]   dma_rotate;
    logic   [3:0]   edge_request;
    logic   [3:0]   dma_request_state;
    logic   [3:0]   encoded_dma;
    logic           end_of_process_internal;
    logic   [3:0]   dma_acknowledge_internal;

    KF8237_Priority_Encoder u_Priority_Encoder (
	 
        .clock                              (clock),
        .reset                              (reset),
		  

        // Internal Bus
        .internal_data_bus                  (internal_data_bus),
		  
        // -- write
        .write_command_register             (write_command_register),
        .write_request_register             (write_request_register),
        .set_or_reset_mask_register         (set_or_reset_mask_register),
        .write_mask_register                (write_mask_register),
		  
        // -- software command
        .master_clear                       (master_clear),
        .clear_mask_register                (clear_mask_register),

        // Internal signals
        .dma_rotate                         (dma_rotate),
        .edge_request                       (edge_request),
        .dma_request_state                  (dma_request_state),
        .encoded_dma                        (encoded_dma),
        .end_of_process_internal            (end_of_process_internal),
        .dma_acknowledge_internal           (dma_acknowledge_internal),

        // External signals
        .dma_request                        (dma_request)
		  
    );


    //
    // Address And Count Registers
    //
    logic   [7:0]   read_address_or_count;
    logic   [3:0]   transfer_register_select;
    logic           initialize_current_register;
    logic           address_hold_config;
    logic           decrement_address_config;
    logic           next_word;
    logic           update_high_address;
    logic           underflow;

    KF8237_Address_And_Count_Registers u_Address_And_Count_Registers (
	 
        .clock                              (clock),
        .reset                              (reset),

        // Internal Bus
        .internal_data_bus                  (internal_data_bus),
        .read_address_or_count              (read_address_or_count),
		  
		  
        // -- write
        .write_base_and_current_address     (write_base_and_current_address),
        .write_base_and_current_word_count  (write_base_and_current_word_count),
		  
		  
        // -- software command
        .clear_byte_pointer                 (clear_byte_pointer),
        .set_byte_pointer                   (set_byte_pointer),
        .master_clear                       (master_clear),
		  
        // -- read
        .read_current_address               (read_current_address),
        .read_current_word_count            (read_current_word_count),

        // Internal signals
        .transfer_register_select           (transfer_register_select),
        .initialize_current_register        (initialize_current_register),
        .address_hold_config                (address_hold_config),
        .decrement_address_config           (decrement_address_config),
        .next_word                          (next_word),
        .update_high_address                (update_high_address),
        .underflow                          (underflow),
        .transfer_address                   (address_out) // Modify shl + bytesel for memory and normal for IO
		  
    );


    //
    // Timing And Control Logic
    //
    logic           output_temporary_data;
    logic   [7:0]   temporary_register;
    logic   [3:0]   terminal_count_state;

    KF8237_Timing_And_Control u_Timing_And_Control (
        .clock                              (clock),
        .reset                              (reset),

        // Internal Bus
        .internal_data_bus                  (internal_data_bus),
		  
        // -- write
        .write_command_register             (write_command_register),
        .write_mode_register                (write_mode_register),
		  
        // -- read
        .read_status_register               (read_status_register),
		  
        // -- software command
        .master_clear                       (master_clear),

        // Internal signals
        .dma_rotate                         (dma_rotate),
        .edge_request                       (edge_request),
        .dma_request_state                  (dma_request_state),
        .encoded_dma                        (encoded_dma),
        .dma_acknowledge_internal           (dma_acknowledge_internal),
        .transfer_register_select           (transfer_register_select),
        .initialize_current_register        (initialize_current_register),
        .address_hold_config                (address_hold_config),
        .decrement_address_config           (decrement_address_config),
        .next_word                          (next_word),
        .update_high_address                (update_high_address),
        .underflow                          (underflow),
        .end_of_process_internal            (end_of_process_internal),
        .lock_bus_control                   (lock_bus_control),
        .output_temporary_data              (output_temporary_data),
        .temporary_register                 (temporary_register),
        .terminal_count_state               (terminal_count_state),

        // External signals
        .hold_request                       (hold_request),
        .hold_acknowledge                   (hold_acknowledge),
        .dma_acknowledge                    (dma_acknowledge),
        .address_enable                     (address_enable),
        .address_strobe                     (address_strobe),
        .output_highst_address              (output_highst_address),
        .memory_read                        (memory_read),
        .memory_write                       (memory_write),
        .io_read_out                        (io_read_n_out),
        .io_read_io                         (io_read_n_io),
        .io_write_out                       (io_write_out),
        .io_write_n_io                      (io_write_n_io),
        .ready                              (ready),
        .end_of_process_in                  (end_of_process_in),
        .end_of_process_out                 (end_of_process_out)
    );


    //
    // Data Bus Buffer & Read/Write Control Logic (2)
    //
    always_comb begin
        if (output_highst_address)
            data_bus_out = address_out[15:8];
        else if ((read_temporary_register) || (output_temporary_data))
            data_bus_out = temporary_register;
        else if (read_status_register)
            data_bus_out = {dma_request_state, terminal_count_state};
        else if ((0 != read_current_address) || (0 != read_current_word_count))
            data_bus_out = read_address_or_count;
        else
            data_bus_out = 8'h00;
    end

endmodule

