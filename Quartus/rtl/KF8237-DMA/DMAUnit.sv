`default_nettype none
module DMAUnit ( input  wire clk,
                 input  wire reset,

                 input  wire dma_chip_select,
                 input  wire dma_page_chip_select,
					  
					  input  wire   [3:0]   dma_device_request,
					  output  logic [3:0]   dma_acknowledge,     // Notify device DMA was completed
	
                 // BUS from CPU
                 input  wire [19:1] m_cpu_addr_in,
                 input  wire [15:0] m_cpu_data_in,
                 input  wire m_cpu_access,
                 input  wire m_cpu_wr_en,
                 output wire cpu_ack,

                 // Memory/IO bus
                 output logic [19:1] m_addr,
                 input  logic [15:0] m_data_in,
                 output logic [15:0] m_data_out,
                 output logic m_access,
                 input  logic m_ack,            // Acknowledge from other unit write performed or read data available	  
                 output logic m_wr_en,          // is a write
					  output logic d_io,             // is an IO port access
                 output logic [1:0] m_bytesel   // Mask for byte to access R/W (0 the byte is ignored)

	 );


    //
    // (DMA Page Register)
    //

    // Generates 4 latches

    logic   [1:0]   bit_select[4] = '{ 2'b00, 2'b01, 2'b10, 2'b11 };
    logic   [3:0]   dma_page_register[4];

    genvar dma_page_i;
    generate
    for (dma_page_i = 0; dma_page_i < 4; dma_page_i = dma_page_i + 1) begin : DMA_PAGE_REGISTERS
        always_ff @(posedge clk or posedge reset) begin
            if (reset)
                dma_page_register[dma_page_i] <= 0;
            else if ((dma_page_chip_select) && m_cpu_access && m_cpu_wr_en && (bit_select[dma_page_i] == m_cpu_addr_in[2:1]))
                dma_page_register[dma_page_i] <= m_cpu_data_in[3:0];
        end
    end
    endgenerate

wire bus_ack;

assign cpu_ack = (dma_page_chip_select & m_cpu_access) | bus_ack;



wire dma_memory_read;

// Bridges the hold signal to make ack immediate
// Bus is not actually holded, CPU can continue to work

wire hold_bridge; 

wire [15:0] dma_address_out;


KF8237 u_KF8237 (

        .clock                              (clk),
        .reset                              (reset),
        .chip_select                        (dma_chip_select),
        .ready                              (/*dma_ready*/),
        .hold_acknowledge                   (hold_bridge),
        .dma_request                        (dma_device_request),         // Request from hardware to perform DMA
        .data_bus_in                        (m_data_in[7:0]),
        .data_bus_out                       (m_data_out),
        .io_read_n_in                       (/*io_read*/),
        .io_read_n_out                      (/*dma_io_read*/),


        .bus_ack(bus_ack),

        //.io_read_n_io                     (),

        .io_write_in                        (m_cpu_access && m_cpu_wr_en), // IO Write from CPU to DMA chip
        .io_write_out                       (/*dma_io_write_n*/),

        //.io_write_n_io                    (),

        .end_of_process_in                  (1'b0),
        .end_of_process_out                 (/*terminal_count*/),
        .address_in                         (m_cpu_addr_in[4:1]),
        .address_out                        (dma_address_out),
        .m_bytesel                          (m_bytesel),

        //.output_highst_address            (),

        .hold_request                       (hold_bridge),
        .dma_acknowledge                    (dma_acknowledge),

        //.address_enable                   (),
        //.address_strobe                   (),

        .memory_read                        (dma_memory_read),
        .memory_write                       (m_wr_en)
    );


assign m_access = dma_memory_read; // | ioread



always_comb begin

        // Default assignment to ensure no inferred latch
        m_addr = {dma_page_register[0], dma_address_out}; // Default or a safe value
	 
        if (/*dma_enable &&*/ |(dma_acknowledge)) begin // If at least one bit is high
		  
            if (dma_acknowledge[2]) begin
                m_addr           = {dma_page_register[1], dma_address_out};
            end
            else if (dma_acknowledge[3]) begin
                m_addr           = {dma_page_register[2], dma_address_out};
            end
            else begin
                m_addr           = {dma_page_register[3], dma_address_out};
            end
        
    end
end



endmodule