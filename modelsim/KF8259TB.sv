`timescale 1ns / 1ps

module KF8259_tb();

    // Testbench Signals
    reg         clk;
    reg         reset;
    reg         chip_select;
    reg         read_enable;
    reg         write_enable;
    reg         address;
    reg [15:0]  data_bus_in;
    wire [15:0] data_bus_out;
    wire        data_bus_io;
    wire        ack;
    reg  [2:0]  cascade_in;
    wire [2:0]  cascade_out;
    wire        cascade_io;
    reg         slave_program_n;
    wire        buffer_enable;
    wire        slave_program_or_enable_buffer;
    reg         interrupt_acknowledge_n;
    wire        interrupt_to_cpu;
    reg  [7:0]  interrupt_request;
    wire [7:0]  irq;
    reg interrupt_acknowledge_simple;

    // Instantiate the Unit Under Test (UUT)
    KF8259 uut (
        .clk(clk),
        .reset(reset),
        .chip_select(chip_select),
        .read_enable(read_enable),
        .write_enable(write_enable),
        .address(address),
        .data_bus_in(data_bus_in),
        .data_bus_out(data_bus_out),
        .data_bus_io(data_bus_io),
        .ack(ack),
        .cascade_in(cascade_in),
        .cascade_out(cascade_out),
        .cascade_io(cascade_io),
        .slave_program_n(slave_program_n),
        .buffer_enable(buffer_enable),
        .slave_program_or_enable_buffer(slave_program_or_enable_buffer),
        .interrupt_acknowledge_n(interrupt_acknowledge_n),
        .interrupt_to_cpu(interrupt_to_cpu),
        .interrupt_request(interrupt_request),
        .interrupt_acknowledge_simple(interrupt_acknowledge_simple),
        .simpleirq(irq)
    );

    // Clock Generation
    initial begin
        clk = 0;
        forever #10 clk = ~clk; // 50MHz Clock
    end
	
	// Send End of Interrupt Command
task sendEOI;
    begin
        chip_select = 1;
        write_enable = 1;
        address = 0; // Assuming address 0 can be used for OCW2 in this setup
        data_bus_in = 16'h0020; // Example EOI command in OCW2 format
        #60; // Wait for the operation to complete

        chip_select = 0;
        write_enable = 0;
    end
endtask


    // Initialization and ICW Programming
    task initializeICWs;
        begin
            // ICW1 - Start initialization sequence
            chip_select = 1;
            write_enable = 1;
            address = 0; // Assuming address 0 is for command writes
            data_bus_in = 16'h0013; // Example ICW1 setup
            #60; // Wait for the operation to complete

            chip_select = 0;
            write_enable = 0;
            #20;

            write_enable = 1;
            chip_select = 1;
            // ICW2 - Set base address of interrupt vectors
            address = 1;
            data_bus_in = 16'h008;  // Example ICW2 setup
            #60; // Wait for the operation to complete

            chip_select = 0;
            write_enable = 0;
            #20;

            write_enable = 1;
            chip_select = 1;
            // ICW4  masks
            data_bus_in = 16'h0001; // Example ICW3 setup for master
            #60; // Wait for the operation to complete

            chip_select = 0;
            write_enable = 0;
            #20;

            write_enable = 1;
            chip_select = 1;
      
            // OCW2 - Set additional operation modes
            data_bus_in = 16'h00ff; // Example ICW4 setup
            #60; // Wait for the operation to complete

            write_enable = 0;
            chip_select = 0;
			
        end
    endtask
	
	
	// Task to simulate raising an interrupt and handling it
    task simulateInterrupt;
        input [7:0] interrupt_number;
        begin
            // Simulate raising an interrupt
            interrupt_request = 1 << interrupt_number;

        end
    endtask
	
	task simpleack;
        
        begin
            
            #20; // Wait for interrupt to be recognized

            // Simulate CPU acknowledging the interrupt using a simple signal
            interrupt_acknowledge_simple = 1'b1; // CPU acknowledges the interrupt
            #100; // Allow time for the interrupt controller to process the acknowledgment

            interrupt_acknowledge_simple = 1'b0; // Reset acknowledgment signal
            
            // Wait a bit to simulate processing time before sending EOI
            #100;

            // Send EOI
            sendEOI();
            
            // Clear the interrupt request
            interrupt_request = 0;
        end
    endtask

    // Test Procedure
    initial begin
        // Initialize Inputs
        reset = 0;
        chip_select = 0;
        read_enable = 0;
        write_enable = 0;
        address = 0;
        data_bus_in = 0;
        cascade_in = 0;
        slave_program_n = 1;
        interrupt_acknowledge_n = 1;
        interrupt_request = 0;
        interrupt_acknowledge_simple = 0;

        // Apply Reset
        #100;
        reset = 1;
        #100;
        reset = 0;
        #100;



        // Initialize the PIC with ICWs
        initializeICWs();

        // Further testing can proceed here, such as triggering interrupts
        // and ensuring the PIC responds as expected.
		
		
		
		#20;
		
		write_enable = 1;
        chip_select = 1;
      
        // OCW2 - Set additional operation modes
        data_bus_in = 16'h0000; // Example ICW4 setup
        #60; // Wait for the operation to complete

        write_enable = 0;
        chip_select = 0;
		
		// Wait for some time to simulate handling of the interrupt
        #200; // Example delay - adjust this value as needed
		
		simulateInterrupt(3);

		
		//#300
		
		
		
		#100
		
		simpleack();
		
		#100
		
		interrupt_request = 0;
		
		#100
		
		// After handling an interrupt, send an EOI command
        sendEOI();

        #1000;
        //$  finish;
    end

endmodule
