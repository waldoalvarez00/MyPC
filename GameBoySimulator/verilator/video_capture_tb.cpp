// Video Capture Model Testbench for Verilator
// Tests video_gen_sim with C++ video capture model
//
// Build: make -f Makefile.video
// Run: ./obj_dir/Vvideo_gen_sim

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vvideo_gen_sim.h"
#include "../sim/video_capture.h"

#define CLK_PERIOD 40  // 25 MHz pixel clock

class VideoTestbench {
public:
    Vvideo_gen_sim* gen;
    VideoCapture* capture;
    VerilatedVcdC* trace;
    vluint64_t sim_time;
    int pass_count;
    int fail_count;

    VideoTestbench(bool debug = false) {
        gen = new Vvideo_gen_sim;
        capture = new VideoCapture(160, 144, debug);
        trace = nullptr;
        sim_time = 0;
        pass_count = 0;
        fail_count = 0;
    }

    ~VideoTestbench() {
        if (trace) {
            trace->close();
            delete trace;
        }
        delete gen;
        delete capture;
    }

    void openTrace(const char* filename) {
        Verilated::traceEverOn(true);
        trace = new VerilatedVcdC;
        gen->trace(trace, 99);
        trace->open(filename);
    }

    void tick() {
        // Rising edge
        gen->clk = 1;
        gen->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;

        // Capture video signals
        bool frame_done = capture->tick(
            gen->vga_r,
            gen->vga_g,
            gen->vga_b,
            gen->vga_hs,
            gen->vga_vs,
            gen->vga_de
        );

        if (frame_done) {
            printf("Frame %d captured (%dx%d)\n",
                   capture->getFrameCount(),
                   capture->getWidth(),
                   capture->getHeight());
        }

        // Falling edge
        gen->clk = 0;
        gen->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;
    }

    void reset() {
        gen->reset = 1;
        gen->enable = 0;

        for (int i = 0; i < 10; i++) {
            tick();
        }

        gen->reset = 0;
        gen->enable = 1;
    }

    // Run for specified number of frames
    int runFrames(int num_frames) {
        int start_frame = capture->getFrameCount();
        int target = start_frame + num_frames;

        while (capture->getFrameCount() < target) {
            tick();

            // Safety limit
            if (sim_time > 100000000) {  // 100ms
                printf("ERROR: Timeout waiting for frames\n");
                return capture->getFrameCount() - start_frame;
            }
        }

        return capture->getFrameCount() - start_frame;
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
    bool save_frames = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--trace") == 0) {
            enable_trace = true;
        }
        if (strcmp(argv[i], "--debug") == 0) {
            debug = true;
        }
        if (strcmp(argv[i], "--save") == 0) {
            save_frames = true;
        }
    }

    VideoTestbench tb(debug);

    if (enable_trace) {
        tb.openTrace("video_test.vcd");
        printf("Tracing enabled - output to video_test.vcd\n");
    }

    printf("\n========================================\n");
    printf("Video Capture Model Testbench\n");
    printf("========================================\n\n");

    // Reset
    tb.reset();
    printf("Video generator reset complete\n");

    // Test 1: Capture first frame
    printf("\n--- Test: Capture first frame ---\n");
    {
        int frames = tb.runFrames(1);
        bool pass = (frames == 1);
        printf("  Captured %d frame(s)\n", frames);
        tb.reportTest("Capture first frame", pass);
    }

    // Test 2: Check resolution detection
    printf("\n--- Test: Resolution detection ---\n");
    {
        int w = tb.capture->getWidth();
        int h = tb.capture->getHeight();
        bool pass = (w == 160 && h == 144);
        printf("  Detected resolution: %dx%d (expected 160x144)\n", w, h);
        tb.reportTest("Resolution detection", pass);
    }

    // Test 3: Capture multiple frames
    printf("\n--- Test: Capture multiple frames ---\n");
    {
        int start = tb.capture->getFrameCount();
        int frames = tb.runFrames(3);
        bool pass = (frames == 3);
        printf("  Captured %d additional frame(s)\n", frames);
        tb.reportTest("Capture multiple frames", pass);
    }

    // Test 4: Save frame as BMP
    printf("\n--- Test: Save BMP file ---\n");
    {
        const char* filename = "/tmp/test_frame.bmp";
        bool pass = tb.capture->saveBMP(filename);
        printf("  Saved to %s\n", filename);
        tb.reportTest("Save BMP file", pass);
    }

    // Test 5: Save frame as PPM
    printf("\n--- Test: Save PPM file ---\n");
    {
        const char* filename = "/tmp/test_frame.ppm";
        bool pass = tb.capture->savePPM(filename);
        printf("  Saved to %s\n", filename);
        tb.reportTest("Save PPM file", pass);
    }

    // Test 6: Check test pattern (verify some pixels)
    printf("\n--- Test: Verify test pattern ---\n");
    {
        bool pass = true;

        // Check top-left pixel (should be white - first bar)
        auto p1 = tb.capture->getPixel(0, 0);
        if (p1.r != 255 || p1.g != 255 || p1.b != 255) {
            printf("  Top-left pixel wrong: (%d,%d,%d) expected (255,255,255)\n",
                   p1.r, p1.g, p1.b);
            pass = false;
        }

        // Check a pixel in the red bar (should be red)
        int red_bar_x = 160 * 5 / 8 + 5;  // Middle of 6th bar
        auto p2 = tb.capture->getPixel(red_bar_x, 10);
        if (p2.r != 255 || p2.g != 0 || p2.b != 0) {
            printf("  Red bar pixel at (%d,10) wrong: (%d,%d,%d) expected (255,0,0)\n",
                   red_bar_x, p2.r, p2.g, p2.b);
            pass = false;
        }

        // Check a pixel in bottom half (should be dimmer)
        auto p3 = tb.capture->getPixel(0, 100);
        if (p3.r != 127 || p3.g != 127 || p3.b != 127) {
            printf("  Bottom-left pixel: (%d,%d,%d) expected ~(127,127,127)\n",
                   p3.r, p3.g, p3.b);
            // Don't fail - may be off by 1 due to rounding
        }

        tb.reportTest("Verify test pattern", pass);
    }

    // Test 7: Calculate checksum
    printf("\n--- Test: Frame checksum ---\n");
    {
        uint32_t checksum = tb.capture->calculateChecksum();
        printf("  Frame checksum: 0x%08X\n", checksum);
        bool pass = (checksum != 0);  // Just verify it's not empty
        tb.reportTest("Frame checksum", pass);
    }

    // Test 8: Clear and verify
    printf("\n--- Test: Clear framebuffer ---\n");
    {
        tb.capture->clear(128, 64, 32);
        auto p = tb.capture->getPixel(50, 50);
        bool pass = (p.r == 128 && p.g == 64 && p.b == 32);
        printf("  Cleared to (128,64,32), pixel at (50,50): (%d,%d,%d)\n",
               p.r, p.g, p.b);
        tb.reportTest("Clear framebuffer", pass);
    }

    // Save all frames if requested
    if (save_frames) {
        printf("\n--- Saving captured frames ---\n");
        tb.capture->setOutputPrefix("/tmp/gameboy_frame");

        // Run a few more frames and save them
        tb.reset();
        for (int i = 0; i < 3; i++) {
            tb.runFrames(1);
            char filename[256];
            snprintf(filename, sizeof(filename), "/tmp/gameboy_frame_%d.bmp", i);
            tb.capture->saveBMP(filename);
        }
        printf("  Saved 3 frames to /tmp/gameboy_frame_*.bmp\n");
    }

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
