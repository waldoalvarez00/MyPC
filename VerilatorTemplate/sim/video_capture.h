// Video Frame Capture Model for Verilator Simulation
// Captures VGA-style video signals and saves as image files
//
// Supports MiSTer-style video interface:
// - 8-bit RGB channels (VGA_R, VGA_G, VGA_B)
// - Sync signals (VGA_HS, VGA_VS)
// - Data enable (VGA_DE)
//
// Output formats: BMP, PPM

#ifndef VIDEO_CAPTURE_H
#define VIDEO_CAPTURE_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

class VideoCapture {
public:
    // Maximum supported resolution
    static const int MAX_WIDTH = 1920;
    static const int MAX_HEIGHT = 1080;

    // Pixel format
    struct Pixel {
        uint8_t r, g, b;
    };

private:
    // Frame buffer
    std::vector<Pixel> framebuffer;
    int width;
    int height;
    int current_x;
    int current_y;

    // Sync detection
    bool prev_hsync;
    bool prev_vsync;
    bool prev_de;

    // Frame counter
    int frame_count;
    bool frame_complete;

    // Timing detection
    int hsync_count;
    int active_width;
    int active_height;
    int max_x_seen;
    int max_y_seen;

    // Configuration
    bool auto_detect_size;
    bool debug_enabled;
    std::string output_prefix;

public:
    VideoCapture(int w = 640, int h = 480, bool debug = false)
        : width(w), height(h), debug_enabled(debug) {
        framebuffer.resize(MAX_WIDTH * MAX_HEIGHT);
        reset();
        auto_detect_size = true;
        output_prefix = "frame";
    }

    void reset() {
        current_x = 0;
        current_y = 0;
        prev_hsync = true;
        prev_vsync = true;
        prev_de = false;
        frame_count = 0;
        frame_complete = false;
        hsync_count = 0;
        active_width = 0;
        active_height = 0;
        max_x_seen = 0;
        max_y_seen = 0;

        // Clear framebuffer
        for (auto& p : framebuffer) {
            p.r = p.g = p.b = 0;
        }
    }

    void setOutputPrefix(const std::string& prefix) {
        output_prefix = prefix;
    }

    void setResolution(int w, int h) {
        width = w;
        height = h;
        auto_detect_size = false;
    }

    void enableAutoDetect(bool enable) {
        auto_detect_size = enable;
    }

    // Main tick function - call every pixel clock
    // Returns true when a complete frame has been captured
    bool tick(
        uint8_t r,      // Red channel (0-255)
        uint8_t g,      // Green channel (0-255)
        uint8_t b,      // Blue channel (0-255)
        bool hsync,     // Horizontal sync (active low typical)
        bool vsync,     // Vertical sync (active low typical)
        bool de         // Data enable (active high = valid pixel)
    ) {
        frame_complete = false;

        // Detect vertical sync (start of new frame)
        // Vsync falling edge = new frame starting
        if (prev_vsync && !vsync) {
            if (frame_count > 0 && max_y_seen > 10) {
                frame_complete = true;

                // Update detected size
                if (auto_detect_size && max_x_seen > 0 && max_y_seen > 0) {
                    active_width = max_x_seen + 1;
                    active_height = max_y_seen + 1;
                    if (debug_enabled) {
                        printf("VIDEO: Frame %d complete, detected size %dx%d\n",
                               frame_count, active_width, active_height);
                    }
                }
            }

            // Reset for new frame
            current_y = 0;
            max_x_seen = 0;
            max_y_seen = 0;
            frame_count++;
        }

        // Detect start of new active line (rising edge of de)
        // This is more reliable than hsync for tracking y position
        if (!prev_de && de) {
            current_x = 0;
            // Only increment y after the first line
            if (max_x_seen > 0) {
                current_y++;
            }
        }

        // Capture pixel if data enable is active
        if (de) {
            if (current_x < MAX_WIDTH && current_y < MAX_HEIGHT) {
                int idx = current_y * MAX_WIDTH + current_x;
                framebuffer[idx].r = r;
                framebuffer[idx].g = g;
                framebuffer[idx].b = b;

                // Track max extents for auto-detection
                if (current_x > max_x_seen) max_x_seen = current_x;
                if (current_y > max_y_seen) max_y_seen = current_y;
            }
            current_x++;
        }

        prev_hsync = hsync;
        prev_vsync = vsync;
        prev_de = de;

        return frame_complete;
    }

    // Alternative tick with active-high sync (some cores use this)
    bool tickActiveHighSync(
        uint8_t r, uint8_t g, uint8_t b,
        bool hsync, bool vsync, bool de
    ) {
        return tick(r, g, b, !hsync, !vsync, de);
    }

    // Get frame count
    int getFrameCount() const {
        return frame_count;
    }

    // Get detected resolution
    int getWidth() const {
        return auto_detect_size ? active_width : width;
    }

    int getHeight() const {
        return auto_detect_size ? active_height : height;
    }

    // Check if a frame is complete
    bool isFrameComplete() const {
        return frame_complete;
    }

    // Get pixel from framebuffer
    Pixel getPixel(int x, int y) const {
        if (x < 0 || x >= MAX_WIDTH || y < 0 || y >= MAX_HEIGHT) {
            return {0, 0, 0};
        }
        return framebuffer[y * MAX_WIDTH + x];
    }

    // Set pixel in framebuffer (for testing)
    void setPixel(int x, int y, uint8_t r, uint8_t g, uint8_t b) {
        if (x >= 0 && x < MAX_WIDTH && y >= 0 && y < MAX_HEIGHT) {
            int idx = y * MAX_WIDTH + x;
            framebuffer[idx].r = r;
            framebuffer[idx].g = g;
            framebuffer[idx].b = b;
        }
    }

    // Save current frame as BMP
    bool saveBMP(const char* filename) {
        int w = getWidth();
        int h = getHeight();

        if (w <= 0 || h <= 0) {
            if (debug_enabled) printf("VIDEO: Cannot save - invalid size %dx%d\n", w, h);
            return false;
        }

        FILE* f = fopen(filename, "wb");
        if (!f) {
            if (debug_enabled) printf("VIDEO: Cannot create file %s\n", filename);
            return false;
        }

        // BMP row size must be multiple of 4 bytes
        int row_size = ((w * 3 + 3) / 4) * 4;
        int padding = row_size - w * 3;
        int data_size = row_size * h;
        int file_size = 54 + data_size;

        // BMP Header
        uint8_t header[54] = {0};

        // Signature
        header[0] = 'B';
        header[1] = 'M';

        // File size
        header[2] = file_size & 0xFF;
        header[3] = (file_size >> 8) & 0xFF;
        header[4] = (file_size >> 16) & 0xFF;
        header[5] = (file_size >> 24) & 0xFF;

        // Data offset
        header[10] = 54;

        // DIB header size
        header[14] = 40;

        // Width
        header[18] = w & 0xFF;
        header[19] = (w >> 8) & 0xFF;
        header[20] = (w >> 16) & 0xFF;
        header[21] = (w >> 24) & 0xFF;

        // Height (negative for top-down)
        int neg_h = -h;
        header[22] = neg_h & 0xFF;
        header[23] = (neg_h >> 8) & 0xFF;
        header[24] = (neg_h >> 16) & 0xFF;
        header[25] = (neg_h >> 24) & 0xFF;

        // Planes
        header[26] = 1;

        // Bits per pixel
        header[28] = 24;

        // Image size
        header[34] = data_size & 0xFF;
        header[35] = (data_size >> 8) & 0xFF;
        header[36] = (data_size >> 16) & 0xFF;
        header[37] = (data_size >> 24) & 0xFF;

        fwrite(header, 1, 54, f);

        // Write pixel data (BGR format, top to bottom)
        uint8_t pad[3] = {0, 0, 0};
        for (int y = 0; y < h; y++) {
            for (int x = 0; x < w; x++) {
                Pixel p = getPixel(x, y);
                uint8_t bgr[3] = {p.b, p.g, p.r};
                fwrite(bgr, 1, 3, f);
            }
            if (padding > 0) {
                fwrite(pad, 1, padding, f);
            }
        }

        fclose(f);
        if (debug_enabled) printf("VIDEO: Saved %s (%dx%d)\n", filename, w, h);
        return true;
    }

    // Save current frame as PPM (simpler format)
    bool savePPM(const char* filename) {
        int w = getWidth();
        int h = getHeight();

        if (w <= 0 || h <= 0) return false;

        FILE* f = fopen(filename, "wb");
        if (!f) return false;

        fprintf(f, "P6\n%d %d\n255\n", w, h);

        for (int y = 0; y < h; y++) {
            for (int x = 0; x < w; x++) {
                Pixel p = getPixel(x, y);
                fputc(p.r, f);
                fputc(p.g, f);
                fputc(p.b, f);
            }
        }

        fclose(f);
        if (debug_enabled) printf("VIDEO: Saved %s (%dx%d)\n", filename, w, h);
        return true;
    }

    // Save frame with automatic filename
    bool saveFrame(const char* format = "bmp") {
        char filename[256];
        snprintf(filename, sizeof(filename), "%s_%04d.%s",
                 output_prefix.c_str(), frame_count, format);

        if (strcmp(format, "ppm") == 0) {
            return savePPM(filename);
        } else {
            return saveBMP(filename);
        }
    }

    // Clear framebuffer
    void clear(uint8_t r = 0, uint8_t g = 0, uint8_t b = 0) {
        for (auto& p : framebuffer) {
            p.r = r;
            p.g = g;
            p.b = b;
        }
    }

    // Generate test pattern
    void generateTestPattern() {
        for (int y = 0; y < height; y++) {
            for (int x = 0; x < width; x++) {
                int idx = y * MAX_WIDTH + x;

                // Color bars
                int bar = (x * 8) / width;
                switch (bar) {
                    case 0: framebuffer[idx] = {255, 255, 255}; break; // White
                    case 1: framebuffer[idx] = {255, 255, 0};   break; // Yellow
                    case 2: framebuffer[idx] = {0, 255, 255};   break; // Cyan
                    case 3: framebuffer[idx] = {0, 255, 0};     break; // Green
                    case 4: framebuffer[idx] = {255, 0, 255};   break; // Magenta
                    case 5: framebuffer[idx] = {255, 0, 0};     break; // Red
                    case 6: framebuffer[idx] = {0, 0, 255};     break; // Blue
                    case 7: framebuffer[idx] = {0, 0, 0};       break; // Black
                }
            }
        }
        active_width = width;
        active_height = height;
    }

    // Compare frames (for testing)
    int compareFrames(const VideoCapture& other) const {
        int w = getWidth();
        int h = getHeight();
        int diff_count = 0;

        if (w != other.getWidth() || h != other.getHeight()) {
            return -1;  // Size mismatch
        }

        for (int y = 0; y < h; y++) {
            for (int x = 0; x < w; x++) {
                Pixel p1 = getPixel(x, y);
                Pixel p2 = other.getPixel(x, y);
                if (p1.r != p2.r || p1.g != p2.g || p1.b != p2.b) {
                    diff_count++;
                }
            }
        }

        return diff_count;
    }

    // Calculate frame checksum (for verification)
    uint32_t calculateChecksum() const {
        uint32_t checksum = 0;
        int w = getWidth();
        int h = getHeight();

        for (int y = 0; y < h; y++) {
            for (int x = 0; x < w; x++) {
                Pixel p = getPixel(x, y);
                checksum += p.r + (p.g << 8) + (p.b << 16);
                checksum = (checksum << 1) | (checksum >> 31);  // Rotate
            }
        }

        return checksum;
    }
};

#endif // VIDEO_CAPTURE_H
