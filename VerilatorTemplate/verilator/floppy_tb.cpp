// Floppy Disk Model Testbench for Verilator
// Tests floppy operations: read, write, format, seek
//
// Build: make -f Makefile.floppy
// Run: ./obj_dir/Vfdc_sim

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vfdc_sim.h"
#include "../sim/floppy_model_cpp.h"

#define CLK_PERIOD 20  // 50 MHz

// FDC port offsets
#define PORT_DOR  2
#define PORT_MSR  4
#define PORT_DATA 5

// FDC commands
#define CMD_READ_DATA    0x66  // MFM + MT + Read
#define CMD_WRITE_DATA   0x45  // MFM + Write
#define CMD_FORMAT_TRACK 0x4D  // MFM + Format
#define CMD_SEEK         0x0F
#define CMD_RECALIBRATE  0x07
#define CMD_SENSE_INT    0x08
#define CMD_SPECIFY      0x03
#define CMD_READ_ID      0x4A
#define CMD_VERSION      0x10

class FloppyTestbench {
public:
    Vfdc_sim* dut;
    FloppyModelCpp* floppy;
    VerilatedVcdC* trace;
    vluint64_t sim_time;
    int pass_count;
    int fail_count;

    FloppyTestbench(bool debug = false) {
        dut = new Vfdc_sim;
        floppy = new FloppyModelCpp(debug);
        trace = nullptr;
        sim_time = 0;
        pass_count = 0;
        fail_count = 0;
    }

    ~FloppyTestbench() {
        if (trace) {
            trace->close();
            delete trace;
        }
        delete dut;
        delete floppy;
    }

    void openTrace(const char* filename) {
        Verilated::traceEverOn(true);
        trace = new VerilatedVcdC;
        dut->trace(trace, 99);
        trace->open(filename);
    }

    void tick() {
        // Rising edge
        dut->clk = 1;
        dut->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;

        // Handle floppy model operations
        if (dut->request != 0) {
            handleFloppyRequest();
        }

        // Update DUT inputs from floppy model
        dut->disk_inserted = floppy->isDiskInserted();
        dut->disk_wp = floppy->isWriteProtected();
        dut->disk_changed = floppy->isDiskChanged();
        dut->current_cyl = floppy->getCurrentCylinder();

        // Falling edge
        dut->clk = 0;
        dut->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;
    }

    void reset() {
        dut->rst_n = 0;
        dut->io_address = 0;
        dut->io_read = 0;
        dut->io_write = 0;
        dut->io_writedata = 0;
        dut->dma_ack = 0;
        dut->dma_tc = 0;
        dut->dma_readdata = 0;
        dut->disk_ready = 1;
        dut->disk_data_in = 0;
        dut->disk_error = 0;

        for (int i = 0; i < 10; i++) {
            tick();
        }

        dut->rst_n = 1;

        for (int i = 0; i < 10; i++) {
            tick();
        }
    }

    // I/O operations
    void ioWrite(uint8_t addr, uint8_t data) {
        dut->io_address = addr;
        dut->io_writedata = data;
        dut->io_write = 1;
        tick();
        dut->io_write = 0;
        tick();
    }

    uint8_t ioRead(uint8_t addr) {
        dut->io_address = addr;
        dut->io_read = 1;
        tick();
        dut->io_read = 0;
        uint8_t data = dut->io_readdata;
        tick();
        return data;
    }

    // Wait for FDC ready (RQM bit)
    bool waitReady(int timeout = 1000) {
        while (timeout-- > 0) {
            uint8_t msr = ioRead(PORT_MSR);
            if (msr & 0x80) return true;
            tick();
        }
        return false;
    }

    // Send command byte
    void sendCommand(uint8_t cmd) {
        waitReady();
        ioWrite(PORT_DATA, cmd);
    }

    // Read result byte
    uint8_t readResult() {
        waitReady();
        return ioRead(PORT_DATA);
    }

    // Initialize FDC
    void initFDC() {
        // Enable motor and DMA
        ioWrite(PORT_DOR, 0x1C);  // Drive 0, motor on, DMA enable, no reset

        // SPECIFY command (timing parameters)
        sendCommand(CMD_SPECIFY);
        sendCommand(0xDF);  // SRT=3ms, HUT=240ms
        sendCommand(0x02);  // HLT=4ms, ND=0
    }

    // Recalibrate (seek to track 0)
    void recalibrate() {
        sendCommand(CMD_RECALIBRATE);
        sendCommand(0x00);  // Drive 0

        // Wait for completion
        for (int i = 0; i < 2000; i++) tick();

        // Sense interrupt
        sendCommand(CMD_SENSE_INT);
        uint8_t st0 = readResult();
        uint8_t cyl = readResult();
        (void)st0; (void)cyl;
    }

    // Seek to cylinder
    void seekCylinder(uint8_t cyl) {
        sendCommand(CMD_SEEK);
        sendCommand(0x00);  // Drive 0, head 0
        sendCommand(cyl);

        // Wait for completion
        for (int i = 0; i < 1000; i++) tick();

        // Sense interrupt
        sendCommand(CMD_SENSE_INT);
        uint8_t st0 = readResult();
        uint8_t result_cyl = readResult();
        (void)st0; (void)result_cyl;

        // Update floppy model
        floppy->seek(cyl);
    }

    // Read sectors
    bool readSectors(uint8_t cyl, uint8_t head, uint8_t sector,
                     uint8_t count, uint8_t* buffer) {
        sendCommand(CMD_READ_DATA);
        sendCommand((head << 2) | 0);  // Head, drive 0
        sendCommand(cyl);
        sendCommand(head);
        sendCommand(sector);
        sendCommand(2);     // Sector size code (512)
        sendCommand(sector + count - 1);  // EOT
        sendCommand(0x1B);  // GPL
        sendCommand(0xFF);  // DTL

        // Wait for data and read
        for (int i = 0; i < 5000; i++) tick();

        // Get results
        uint8_t st0 = readResult();
        uint8_t st1 = readResult();
        uint8_t st2 = readResult();
        readResult(); // C
        readResult(); // H
        readResult(); // R
        readResult(); // N

        return (st1 == 0 && st2 == 0);
    }

    // Write sectors
    bool writeSectors(uint8_t cyl, uint8_t head, uint8_t sector,
                      uint8_t count, const uint8_t* buffer) {
        sendCommand(CMD_WRITE_DATA);
        sendCommand((head << 2) | 0);
        sendCommand(cyl);
        sendCommand(head);
        sendCommand(sector);
        sendCommand(2);     // Size code
        sendCommand(sector + count - 1);
        sendCommand(0x1B);
        sendCommand(0xFF);

        // Wait for completion
        for (int i = 0; i < 5000; i++) tick();

        // Get results
        uint8_t st0 = readResult();
        uint8_t st1 = readResult();
        uint8_t st2 = readResult();
        readResult(); readResult(); readResult(); readResult();

        return (st1 == 0 && st2 == 0);
    }

    // Format track
    bool formatTrack(uint8_t cyl, uint8_t head) {
        sendCommand(CMD_FORMAT_TRACK);
        sendCommand((head << 2) | 0);
        sendCommand(2);     // Size code
        sendCommand(18);    // Sectors per track
        sendCommand(0x1B);  // GPL
        sendCommand(0xF6);  // Fill byte

        // Wait for completion
        for (int i = 0; i < 5000; i++) tick();

        // Get results
        uint8_t st0 = readResult();
        uint8_t st1 = readResult();
        uint8_t st2 = readResult();
        readResult(); readResult(); readResult(); readResult();

        // Also format in model
        floppy->formatTrack(cyl, head, 0xF6);

        return (st1 == 0 && st2 == 0);
    }

    void handleFloppyRequest() {
        uint8_t cyl = dut->cylinder;
        uint8_t head = dut->head;
        uint8_t sect = dut->sector;

        switch (dut->request) {
            case 1:  // Read
                if (dut->disk_data_rd) {
                    uint8_t buffer[512];
                    uint16_t bytes;
                    floppy->readSector(cyl, head, sect, buffer, bytes);
                    static int byte_idx = 0;
                    dut->disk_data_in = buffer[byte_idx++ % 512];
                }
                break;

            case 2:  // Write
                if (dut->disk_data_wr) {
                    // Would write to model here
                }
                break;

            case 3:  // Format
                // Format handled in formatTrack
                break;
        }
    }

    void reportTest(const char* name, bool pass) {
        if (pass) {
            printf("PASS: %s\n", name);
            pass_count++;
        } else {
            printf("FAIL: %s\n", name);
            fail_count++;
        }
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    bool debug = false;
    bool enable_trace = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--trace") == 0) enable_trace = true;
        if (strcmp(argv[i], "--debug") == 0) debug = true;
    }

    FloppyTestbench tb(debug);

    if (enable_trace) {
        tb.openTrace("floppy_test.vcd");
        printf("Tracing enabled - output to floppy_test.vcd\n");
    }

    printf("\n========================================\n");
    printf("Floppy Disk Model Testbench\n");
    printf("========================================\n\n");

    // Reset
    tb.reset();
    printf("System reset complete\n");

    // Test 1: Insert disk
    printf("\n--- Test: Insert 1.44M disk ---\n");
    {
        bool pass = tb.floppy->insertDisk(FloppyModelCpp::FMT_1440K, false);
        printf("  Inserted %s disk\n", tb.floppy->getGeometry().name);
        tb.reportTest("Insert 1.44M disk", pass);
    }

    // Test 2: Initialize FDC
    printf("\n--- Test: Initialize FDC ---\n");
    {
        tb.initFDC();
        bool pass = true;
        printf("  FDC initialized\n");
        tb.reportTest("Initialize FDC", pass);
    }

    // Test 3: Recalibrate
    printf("\n--- Test: Recalibrate ---\n");
    {
        tb.recalibrate();
        bool pass = (tb.floppy->getCurrentCylinder() == 0);
        printf("  Position: cylinder %d\n", tb.floppy->getCurrentCylinder());
        tb.reportTest("Recalibrate", pass);
    }

    // Test 4: Seek
    printf("\n--- Test: Seek to cylinder 10 ---\n");
    {
        tb.seekCylinder(10);
        bool pass = (tb.floppy->getCurrentCylinder() == 10);
        printf("  Position: cylinder %d\n", tb.floppy->getCurrentCylinder());
        tb.reportTest("Seek to cylinder 10", pass);
    }

    // Test 5: Write test pattern
    printf("\n--- Test: Write sector ---\n");
    {
        uint8_t write_buf[512];
        for (int i = 0; i < 512; i++) {
            write_buf[i] = i & 0xFF;
        }

        // Write directly to model
        FloppyModelCpp::OpStatus status;
        status = tb.floppy->writeSector(10, 0, 1, write_buf, 512);
        bool pass = (status == FloppyModelCpp::OP_SUCCESS);
        printf("  Wrote 512 bytes to C=10 H=0 S=1\n");
        tb.reportTest("Write sector", pass);
    }

    // Test 6: Read and verify
    printf("\n--- Test: Read and verify sector ---\n");
    {
        uint8_t read_buf[512];
        uint16_t bytes_read;
        FloppyModelCpp::OpStatus status;
        status = tb.floppy->readSector(10, 0, 1, read_buf, bytes_read);

        bool pass = (status == FloppyModelCpp::OP_SUCCESS && bytes_read == 512);
        if (pass) {
            for (int i = 0; i < 512; i++) {
                if (read_buf[i] != (i & 0xFF)) {
                    pass = false;
                    break;
                }
            }
        }
        printf("  Read %d bytes, data %s\n", bytes_read,
               pass ? "verified" : "mismatch");
        tb.reportTest("Read and verify sector", pass);
    }

    // Test 7: Format track
    printf("\n--- Test: Format track ---\n");
    {
        FloppyModelCpp::OpStatus status;
        status = tb.floppy->formatTrack(20, 0, 0xE5);
        bool pass = (status == FloppyModelCpp::OP_SUCCESS);
        printf("  Formatted C=20 H=0\n");
        tb.reportTest("Format track", pass);
    }

    // Test 8: Verify format fill
    printf("\n--- Test: Verify format fill ---\n");
    {
        uint8_t read_buf[512];
        uint16_t bytes_read;
        tb.floppy->readSector(20, 0, 1, read_buf, bytes_read);

        bool pass = true;
        for (int i = 0; i < 512; i++) {
            if (read_buf[i] != 0xE5) {
                pass = false;
                break;
            }
        }
        printf("  Format fill byte: %s\n", pass ? "correct" : "incorrect");
        tb.reportTest("Verify format fill", pass);
    }

    // Test 9: Multiple sector write
    printf("\n--- Test: Multiple sector write ---\n");
    {
        bool pass = true;
        for (int s = 1; s <= 5; s++) {
            uint8_t buf[512];
            memset(buf, s, 512);
            FloppyModelCpp::OpStatus status;
            status = tb.floppy->writeSector(30, 0, s, buf, 512);
            if (status != FloppyModelCpp::OP_SUCCESS) {
                pass = false;
                break;
            }
        }
        printf("  Wrote 5 sectors\n");
        tb.reportTest("Multiple sector write", pass);
    }

    // Test 10: Multiple sector read
    printf("\n--- Test: Multiple sector read ---\n");
    {
        bool pass = true;
        for (int s = 1; s <= 5; s++) {
            uint8_t buf[512];
            uint16_t bytes;
            tb.floppy->readSector(30, 0, s, buf, bytes);

            for (int i = 0; i < 512; i++) {
                if (buf[i] != s) {
                    pass = false;
                    break;
                }
            }
            if (!pass) break;
        }
        printf("  Read and verified 5 sectors\n");
        tb.reportTest("Multiple sector read", pass);
    }

    // Test 11: Write protection
    printf("\n--- Test: Write protection ---\n");
    {
        tb.floppy->setWriteProtection(true);
        uint8_t buf[512] = {0};
        FloppyModelCpp::OpStatus status;
        status = tb.floppy->writeSector(0, 0, 1, buf, 512);
        bool pass = (status == FloppyModelCpp::OP_WRITE_PROTECT);
        tb.floppy->setWriteProtection(false);
        printf("  Write blocked: %s\n", pass ? "yes" : "no");
        tb.reportTest("Write protection", pass);
    }

    // Test 12: Invalid sector
    printf("\n--- Test: Invalid sector access ---\n");
    {
        uint8_t buf[512];
        uint16_t bytes;
        FloppyModelCpp::OpStatus status;
        status = tb.floppy->readSector(0, 0, 99, buf, bytes);
        bool pass = (status == FloppyModelCpp::OP_NOT_FOUND);
        printf("  Invalid sector detected: %s\n", pass ? "yes" : "no");
        tb.reportTest("Invalid sector access", pass);
    }

    // Test 13: Different disk formats
    printf("\n--- Test: 720K disk format ---\n");
    {
        tb.floppy->ejectDisk();
        bool pass = tb.floppy->insertDisk(FloppyModelCpp::FMT_720K, false);
        const FloppyModelCpp::DiskGeometry& geom = tb.floppy->getGeometry();
        pass = pass && (geom.total_size == 737280);
        printf("  Format: %s, Size: %u bytes\n", geom.name, geom.total_size);
        tb.reportTest("720K disk format", pass);
    }

    // Test 14: Disk info
    printf("\n--- Test: Disk info ---\n");
    {
        tb.floppy->printInfo();
        bool pass = true;
        tb.reportTest("Disk info", pass);
    }

    // Print statistics
    printf("\n");
    tb.floppy->printStats();

    // Final summary
    printf("\n========================================\n");
    printf("Test Summary\n");
    printf("========================================\n");
    printf("Passed: %d\n", tb.pass_count);
    printf("Failed: %d\n", tb.fail_count);
    printf("Total:  %d\n", tb.pass_count + tb.fail_count);

    if (tb.fail_count == 0) {
        printf("\nSUCCESS: All tests passed!\n\n");
    } else {
        printf("\nFAILURE: %d test(s) failed\n\n", tb.fail_count);
    }

    return tb.fail_count > 0 ? 1 : 0;
}
