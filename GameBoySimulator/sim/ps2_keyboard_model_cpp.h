// PS/2 Keyboard Model for Verilator Simulation
// Supports PS/2 protocol with scan code generation
//
// Features:
// - PS/2 protocol (clock/data timing)
// - Scan code sets (Set 1, Set 2, Set 3)
// - Key press/release with make/break codes
// - Special keys handling
// - LED control (Caps, Num, Scroll Lock)
// - Command response (identify, reset, echo)

#ifndef PS2_KEYBOARD_MODEL_CPP_H
#define PS2_KEYBOARD_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <queue>
#include <vector>

class PS2KeyboardModelCpp {
public:
    // Scan code sets
    enum ScanCodeSet {
        SCAN_SET_1 = 1,
        SCAN_SET_2 = 2,
        SCAN_SET_3 = 3
    };

    // Key codes (virtual key codes)
    enum KeyCode {
        KEY_NONE = 0,
        // Letters
        KEY_A = 0x04, KEY_B, KEY_C, KEY_D, KEY_E, KEY_F, KEY_G, KEY_H,
        KEY_I, KEY_J, KEY_K, KEY_L, KEY_M, KEY_N, KEY_O, KEY_P,
        KEY_Q, KEY_R, KEY_S, KEY_T, KEY_U, KEY_V, KEY_W, KEY_X,
        KEY_Y, KEY_Z,
        // Numbers
        KEY_1 = 0x1E, KEY_2, KEY_3, KEY_4, KEY_5, KEY_6, KEY_7, KEY_8, KEY_9, KEY_0,
        // Function keys
        KEY_F1 = 0x3A, KEY_F2, KEY_F3, KEY_F4, KEY_F5, KEY_F6,
        KEY_F7, KEY_F8, KEY_F9, KEY_F10, KEY_F11, KEY_F12,
        // Special keys
        KEY_ESC = 0x29, KEY_TAB = 0x2B, KEY_CAPS = 0x39,
        KEY_LSHIFT = 0xE1, KEY_RSHIFT = 0xE5,
        KEY_LCTRL = 0xE0, KEY_RCTRL = 0xE4,
        KEY_LALT = 0xE2, KEY_RALT = 0xE6,
        KEY_SPACE = 0x2C, KEY_ENTER = 0x28, KEY_BACKSPACE = 0x2A,
        // Arrow keys
        KEY_UP = 0x52, KEY_DOWN = 0x51, KEY_LEFT = 0x50, KEY_RIGHT = 0x4F,
        // Other
        KEY_INSERT = 0x49, KEY_DELETE = 0x4C, KEY_HOME = 0x4A, KEY_END = 0x4D,
        KEY_PAGEUP = 0x4B, KEY_PAGEDOWN = 0x4E,
        KEY_NUMLOCK = 0x53, KEY_SCROLLLOCK = 0x47, KEY_PAUSE = 0x48
    };

    // PS/2 commands from host
    enum PS2Command {
        CMD_RESET = 0xFF,
        CMD_RESEND = 0xFE,
        CMD_SET_DEFAULT = 0xF6,
        CMD_DISABLE = 0xF5,
        CMD_ENABLE = 0xF4,
        CMD_SET_RATE = 0xF3,
        CMD_READ_ID = 0xF2,
        CMD_SET_SCAN_SET = 0xF0,
        CMD_ECHO = 0xEE,
        CMD_SET_LEDS = 0xED
    };

    // PS/2 responses
    enum PS2Response {
        RESP_ACK = 0xFA,
        RESP_RESEND = 0xFE,
        RESP_ERROR = 0xFC,
        RESP_BAT_OK = 0xAA,
        RESP_ECHO = 0xEE
    };

    // LED bits
    enum LEDMask {
        LED_SCROLL = 0x01,
        LED_NUM = 0x02,
        LED_CAPS = 0x04
    };

private:
    // State
    bool enabled;
    ScanCodeSet scan_set;
    uint8_t led_state;
    uint8_t typematic_rate;
    uint8_t typematic_delay;

    // Output buffer (scan codes to send)
    std::queue<uint8_t> output_buffer;

    // Command state
    bool waiting_for_param;
    uint8_t pending_command;

    // PS/2 line state
    bool clock_line;
    bool data_line;
    int bit_count;
    uint8_t shift_reg;
    bool parity;

    // Timing
    int clock_divider;
    int bit_timer;

    // Statistics
    uint32_t keys_pressed;
    uint32_t keys_released;
    uint32_t commands_received;

    // Debug
    bool debug_enabled;

    // Set 2 scan codes for common keys
    static const uint8_t SCANCODE_SET2[256];

public:
    PS2KeyboardModelCpp(bool debug = false)
        : debug_enabled(debug) {
        reset();
    }

    void reset() {
        enabled = true;
        scan_set = SCAN_SET_2;
        led_state = 0;
        typematic_rate = 0x0B;  // 10.9 chars/sec
        typematic_delay = 0x01; // 500ms

        while (!output_buffer.empty()) output_buffer.pop();

        waiting_for_param = false;
        pending_command = 0;

        clock_line = true;
        data_line = true;
        bit_count = 0;
        shift_reg = 0;
        parity = false;

        clock_divider = 0;
        bit_timer = 0;

        keys_pressed = 0;
        keys_released = 0;
        commands_received = 0;

        // Send BAT (Basic Assurance Test) success
        queueByte(RESP_BAT_OK);

        if (debug_enabled) {
            printf("PS2KB: Reset complete\n");
        }
    }

    // Press a key
    void keyPress(uint8_t keycode) {
        if (!enabled) return;

        uint8_t scancode = getScanCode(keycode, false);
        if (scancode == 0) return;

        // Check for extended keys
        if (isExtendedKey(keycode)) {
            queueByte(0xE0);
        }

        queueByte(scancode);
        keys_pressed++;

        if (debug_enabled) {
            printf("PS2KB: Key press 0x%02X -> scan 0x%02X\n", keycode, scancode);
        }
    }

    // Release a key
    void keyRelease(uint8_t keycode) {
        if (!enabled) return;

        uint8_t scancode = getScanCode(keycode, false);
        if (scancode == 0) return;

        // Check for extended keys
        if (isExtendedKey(keycode)) {
            queueByte(0xE0);
        }

        // Break code
        if (scan_set == SCAN_SET_1) {
            queueByte(scancode | 0x80);
        } else {
            queueByte(0xF0);  // Break prefix for Set 2
            queueByte(scancode);
        }

        keys_released++;

        if (debug_enabled) {
            printf("PS2KB: Key release 0x%02X\n", keycode);
        }
    }

    // Type a character (press and release)
    void typeKey(uint8_t keycode) {
        keyPress(keycode);
        keyRelease(keycode);
    }

    // Type a string
    void typeString(const char* str) {
        while (*str) {
            uint8_t keycode = charToKeycode(*str);
            if (keycode != KEY_NONE) {
                // Check if shift needed
                if (needsShift(*str)) {
                    keyPress(KEY_LSHIFT);
                    typeKey(keycode);
                    keyRelease(KEY_LSHIFT);
                } else {
                    typeKey(keycode);
                }
            }
            str++;
        }
    }

    // Process command from host
    void receiveCommand(uint8_t cmd) {
        commands_received++;

        if (waiting_for_param) {
            // This is a parameter for previous command
            handleParameter(cmd);
            return;
        }

        if (debug_enabled) {
            printf("PS2KB: Received command 0x%02X\n", cmd);
        }

        switch (cmd) {
            case CMD_RESET:
                queueByte(RESP_ACK);
                // Don't call full reset() which clears buffer - just send BAT
                queueByte(RESP_BAT_OK);
                enabled = true;
                scan_set = SCAN_SET_2;
                led_state = 0;
                break;

            case CMD_RESEND:
                // Resend last byte (simplified)
                queueByte(RESP_ACK);
                break;

            case CMD_SET_DEFAULT:
                queueByte(RESP_ACK);
                scan_set = SCAN_SET_2;
                typematic_rate = 0x0B;
                typematic_delay = 0x01;
                break;

            case CMD_DISABLE:
                queueByte(RESP_ACK);
                enabled = false;
                break;

            case CMD_ENABLE:
                queueByte(RESP_ACK);
                enabled = true;
                break;

            case CMD_SET_RATE:
                queueByte(RESP_ACK);
                waiting_for_param = true;
                pending_command = cmd;
                break;

            case CMD_READ_ID:
                queueByte(RESP_ACK);
                queueByte(0xAB);  // Keyboard ID byte 1
                queueByte(0x83);  // Keyboard ID byte 2 (MF2)
                break;

            case CMD_SET_SCAN_SET:
                queueByte(RESP_ACK);
                waiting_for_param = true;
                pending_command = cmd;
                break;

            case CMD_ECHO:
                queueByte(RESP_ECHO);
                break;

            case CMD_SET_LEDS:
                queueByte(RESP_ACK);
                waiting_for_param = true;
                pending_command = cmd;
                break;

            default:
                queueByte(RESP_ACK);
                break;
        }
    }

    // Get next byte to send (for PS/2 protocol)
    bool getNextByte(uint8_t& byte) {
        if (output_buffer.empty()) {
            return false;
        }
        byte = output_buffer.front();
        output_buffer.pop();
        return true;
    }

    // Check if data available
    bool hasData() const {
        return !output_buffer.empty();
    }

    // Get buffer size
    int getBufferSize() const {
        return (int)output_buffer.size();
    }

    // LED state
    uint8_t getLEDState() const { return led_state; }
    bool isCapsLock() const { return led_state & LED_CAPS; }
    bool isNumLock() const { return led_state & LED_NUM; }
    bool isScrollLock() const { return led_state & LED_SCROLL; }

    // State accessors
    bool isEnabled() const { return enabled; }
    ScanCodeSet getScanSet() const { return scan_set; }

    // Statistics
    uint32_t getKeysPressed() const { return keys_pressed; }
    uint32_t getKeysReleased() const { return keys_released; }
    uint32_t getCommandsReceived() const { return commands_received; }

    void printStats() const {
        printf("PS/2 Keyboard Statistics:\n");
        printf("  Keys pressed:  %u\n", keys_pressed);
        printf("  Keys released: %u\n", keys_released);
        printf("  Commands:      %u\n", commands_received);
        printf("  LED state:     0x%02X\n", led_state);
    }

    // Direct scan code injection (for testing)
    void injectScanCode(uint8_t code) {
        queueByte(code);
    }

    // Inject multiple scan codes
    void injectScanCodes(const uint8_t* codes, int count) {
        for (int i = 0; i < count; i++) {
            queueByte(codes[i]);
        }
    }

private:
    void queueByte(uint8_t byte) {
        output_buffer.push(byte);
    }

    void handleParameter(uint8_t param) {
        waiting_for_param = false;

        switch (pending_command) {
            case CMD_SET_RATE:
                typematic_rate = param & 0x1F;
                typematic_delay = (param >> 5) & 0x03;
                queueByte(RESP_ACK);
                break;

            case CMD_SET_SCAN_SET:
                if (param == 0) {
                    // Query current set
                    queueByte(RESP_ACK);
                    queueByte(scan_set);
                } else if (param >= 1 && param <= 3) {
                    scan_set = (ScanCodeSet)param;
                    queueByte(RESP_ACK);
                } else {
                    queueByte(RESP_ERROR);
                }
                break;

            case CMD_SET_LEDS:
                led_state = param & 0x07;
                queueByte(RESP_ACK);
                if (debug_enabled) {
                    printf("PS2KB: LEDs set to 0x%02X (Caps=%d Num=%d Scroll=%d)\n",
                           led_state, isCapsLock(), isNumLock(), isScrollLock());
                }
                break;

            default:
                queueByte(RESP_ACK);
                break;
        }
    }

    uint8_t getScanCode(uint8_t keycode, bool release) {
        // Simplified mapping - would need full table for production
        if (keycode < 128) {
            return SCANCODE_SET2[keycode];
        }

        // Extended keys (modifier keys with E0 prefix)
        // These are Set 2 scan codes for extended keys
        switch (keycode) {
            case KEY_LCTRL:  return 0x14;  // Left Ctrl
            case KEY_LSHIFT: return 0x12;  // Left Shift
            case KEY_LALT:   return 0x11;  // Left Alt
            case KEY_RCTRL:  return 0x14;  // Right Ctrl (with E0)
            case KEY_RSHIFT: return 0x59;  // Right Shift
            case KEY_RALT:   return 0x11;  // Right Alt (with E0)
            default:         return 0x00;
        }
    }

    bool isExtendedKey(uint8_t keycode) {
        // Extended keys use E0 prefix
        switch (keycode) {
            case KEY_RCTRL:
            case KEY_RALT:
            case KEY_INSERT:
            case KEY_DELETE:
            case KEY_HOME:
            case KEY_END:
            case KEY_PAGEUP:
            case KEY_PAGEDOWN:
            case KEY_UP:
            case KEY_DOWN:
            case KEY_LEFT:
            case KEY_RIGHT:
                return true;
            default:
                return false;
        }
    }

    uint8_t charToKeycode(char c) {
        if (c >= 'a' && c <= 'z') return KEY_A + (c - 'a');
        if (c >= 'A' && c <= 'Z') return KEY_A + (c - 'A');
        if (c >= '1' && c <= '9') return KEY_1 + (c - '1');
        if (c == '0') return KEY_0;
        if (c == ' ') return KEY_SPACE;
        if (c == '\n' || c == '\r') return KEY_ENTER;
        if (c == '\t') return KEY_TAB;
        if (c == '\b') return KEY_BACKSPACE;
        return KEY_NONE;
    }

    bool needsShift(char c) {
        return (c >= 'A' && c <= 'Z') ||
               c == '!' || c == '@' || c == '#' || c == '$' ||
               c == '%' || c == '^' || c == '&' || c == '*' ||
               c == '(' || c == ')' || c == '_' || c == '+';
    }
};

// Set 2 scan codes for basic keys
// Index is keycode, value is Set 2 scan code
const uint8_t PS2KeyboardModelCpp::SCANCODE_SET2[256] = {
    // 0x00-0x0F
    0x00, 0x00, 0x00, 0x00, 0x1C, 0x32, 0x21, 0x23,  // 0x00-0x07: -, -, -, -, A, B, C, D
    0x24, 0x2B, 0x34, 0x33, 0x43, 0x3B, 0x42, 0x4B,  // 0x08-0x0F: E, F, G, H, I, J, K, L
    // 0x10-0x1F
    0x3A, 0x31, 0x44, 0x4D, 0x15, 0x2D, 0x1B, 0x2C,  // 0x10-0x17: M, N, O, P, Q, R, S, T
    0x3C, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x16, 0x1E,  // 0x18-0x1F: U, V, -, -, -, -, 1, 2
    // 0x20-0x2F
    0x26, 0x25, 0x2E, 0x36, 0x3D, 0x3E, 0x46, 0x45,  // 0x20-0x27: 3, 4, 5, 6, 7, 8, 9, 0
    0x5A, 0x76, 0x66, 0x0D, 0x29, 0x00, 0x00, 0x00,  // 0x28-0x2F: Enter, Esc, Backspace, Tab, Space
    // 0x30-0x3F
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // 0x30-0x37
    0x00, 0x58, 0x05, 0x06, 0x04, 0x0C, 0x03, 0x0B,  // 0x38-0x3F: -, Caps, F1, F2, F3, F4, F5, F6
    // 0x40-0x4F
    0x83, 0x0A, 0x01, 0x09, 0x78, 0x07, 0x00, 0x00,  // 0x40-0x47: F7, F8, F9, F10, F11, F12
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x74,  // 0x48-0x4F: -, Insert, Home, PgUp, Del, End, PgDn, Right
    // 0x50-0x5F
    0x6B, 0x72, 0x75, 0x00, 0x00, 0x00, 0x00, 0x00,  // 0x50-0x57: Left, Down, Up
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // 0x58-0x5F
    // Remaining 0x60-0xFF filled with zeros
};

#endif // PS2_KEYBOARD_MODEL_CPP_H
