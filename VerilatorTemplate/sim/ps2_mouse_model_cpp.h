// PS/2 Mouse Model for Verilator Simulation
// Supports standard 3-byte and Intellimouse 4-byte protocols
//
// Features:
// - Standard PS/2 mouse (3-byte packets)
// - Intellimouse with scroll wheel (4-byte packets)
// - 5-button mouse support
// - Movement and button handling
// - Command response (identify, reset, set rate, set resolution)
// - Stream and remote modes

#ifndef PS2_MOUSE_MODEL_CPP_H
#define PS2_MOUSE_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <queue>
#include <cmath>

class PS2MouseModelCpp {
public:
    // Mouse types
    enum MouseType {
        MOUSE_STANDARD = 0x00,    // 3-byte packets
        MOUSE_WHEEL = 0x03,       // 4-byte packets (Intellimouse)
        MOUSE_5BUTTON = 0x04      // 4-byte packets with buttons 4/5
    };

    // Button masks
    enum ButtonMask {
        BTN_LEFT = 0x01,
        BTN_RIGHT = 0x02,
        BTN_MIDDLE = 0x04,
        BTN_4 = 0x08,
        BTN_5 = 0x10
    };

    // PS/2 mouse commands
    enum PS2Command {
        CMD_RESET = 0xFF,
        CMD_RESEND = 0xFE,
        CMD_SET_DEFAULTS = 0xF6,
        CMD_DISABLE_REPORTING = 0xF5,
        CMD_ENABLE_REPORTING = 0xF4,
        CMD_SET_SAMPLE_RATE = 0xF3,
        CMD_GET_DEVICE_ID = 0xF2,
        CMD_SET_REMOTE_MODE = 0xF0,
        CMD_SET_WRAP_MODE = 0xEE,
        CMD_RESET_WRAP_MODE = 0xEC,
        CMD_READ_DATA = 0xEB,
        CMD_SET_STREAM_MODE = 0xEA,
        CMD_STATUS_REQUEST = 0xE9,
        CMD_SET_RESOLUTION = 0xE8,
        CMD_SET_SCALING_2_1 = 0xE7,
        CMD_SET_SCALING_1_1 = 0xE6
    };

    // PS/2 responses
    enum PS2Response {
        RESP_ACK = 0xFA,
        RESP_RESEND = 0xFE,
        RESP_ERROR = 0xFC,
        RESP_BAT_OK = 0xAA
    };

    // Resolution values (counts per mm)
    enum Resolution {
        RES_1_COUNT = 0,   // 1 count/mm
        RES_2_COUNT = 1,   // 2 counts/mm
        RES_4_COUNT = 2,   // 4 counts/mm
        RES_8_COUNT = 3    // 8 counts/mm
    };

private:
    // State
    MouseType mouse_type;
    bool enabled;
    bool stream_mode;
    bool wrap_mode;
    uint8_t sample_rate;
    uint8_t resolution;
    bool scaling_2_1;

    // Button state
    uint8_t button_state;

    // Accumulated movement
    int16_t accum_x;
    int16_t accum_y;
    int8_t accum_z;  // Scroll wheel

    // Output buffer
    std::queue<uint8_t> output_buffer;

    // Command state
    bool waiting_for_param;
    uint8_t pending_command;

    // Intellimouse detection sequence
    int intellimouse_seq;

    // Statistics
    uint32_t packets_sent;
    uint32_t commands_received;

    // Debug
    bool debug_enabled;

public:
    PS2MouseModelCpp(bool debug = false)
        : debug_enabled(debug) {
        reset();
    }

    void reset() {
        mouse_type = MOUSE_STANDARD;
        enabled = false;
        stream_mode = true;
        wrap_mode = false;
        sample_rate = 100;
        resolution = RES_4_COUNT;
        scaling_2_1 = false;

        button_state = 0;
        accum_x = 0;
        accum_y = 0;
        accum_z = 0;

        while (!output_buffer.empty()) output_buffer.pop();

        waiting_for_param = false;
        pending_command = 0;
        intellimouse_seq = 0;

        packets_sent = 0;
        commands_received = 0;

        // Send BAT success and device ID
        queueByte(RESP_BAT_OK);
        queueByte(mouse_type);

        if (debug_enabled) {
            printf("PS2MOUSE: Reset complete\n");
        }
    }

    // Set button state
    void setButton(uint8_t button, bool pressed) {
        if (pressed) {
            button_state |= button;
        } else {
            button_state &= ~button;
        }

        if (debug_enabled) {
            printf("PS2MOUSE: Button 0x%02X %s (state=0x%02X)\n",
                   button, pressed ? "pressed" : "released", button_state);
        }
    }

    // Move mouse (relative)
    void move(int dx, int dy) {
        accum_x += dx;
        accum_y += dy;

        // Clamp to 9-bit signed range (allows overflow detection)
        if (accum_x > 511) accum_x = 511;
        if (accum_x < -512) accum_x = -512;
        if (accum_y > 511) accum_y = 511;
        if (accum_y < -512) accum_y = -512;

        if (debug_enabled) {
            printf("PS2MOUSE: Move dx=%d dy=%d (accum x=%d y=%d)\n",
                   dx, dy, accum_x, accum_y);
        }
    }

    // Scroll wheel
    void scroll(int dz) {
        if (mouse_type == MOUSE_STANDARD) return;

        accum_z += dz;
        if (accum_z > 7) accum_z = 7;
        if (accum_z < -8) accum_z = -8;

        if (debug_enabled) {
            printf("PS2MOUSE: Scroll dz=%d (accum z=%d)\n", dz, accum_z);
        }
    }

    // Generate and send mouse packet
    void sendPacket() {
        if (!enabled || !stream_mode) return;

        // Build packet
        uint8_t byte1 = 0x08;  // Bit 3 always 1

        // Buttons
        byte1 |= (button_state & BTN_LEFT) ? 0x01 : 0;
        byte1 |= (button_state & BTN_RIGHT) ? 0x02 : 0;
        byte1 |= (button_state & BTN_MIDDLE) ? 0x04 : 0;

        // Apply scaling if enabled
        int16_t x = accum_x;
        int16_t y = accum_y;

        if (scaling_2_1) {
            x = applyScaling(x);
            y = applyScaling(y);
        }

        // Check overflow BEFORE clamping
        bool x_overflow = (x > 255 || x < -256);
        bool y_overflow = (y > 255 || y < -256);

        // Clamp to byte range
        int8_t dx = (x > 127) ? 127 : ((x < -128) ? -128 : x);
        int8_t dy = (y > 127) ? 127 : ((y < -128) ? -128 : y);

        // Sign bits
        if (dx < 0) byte1 |= 0x10;
        if (dy < 0) byte1 |= 0x20;

        // Overflow bits
        if (x_overflow) byte1 |= 0x40;
        if (y_overflow) byte1 |= 0x80;

        // Queue packet bytes
        queueByte(byte1);
        queueByte((uint8_t)dx);
        queueByte((uint8_t)dy);

        // Add scroll/buttons for wheel mouse
        if (mouse_type == MOUSE_WHEEL) {
            queueByte((uint8_t)(accum_z & 0x0F));
        } else if (mouse_type == MOUSE_5BUTTON) {
            uint8_t byte4 = accum_z & 0x0F;
            if (button_state & BTN_4) byte4 |= 0x10;
            if (button_state & BTN_5) byte4 |= 0x20;
            queueByte(byte4);
        }

        // Clear accumulators
        accum_x = 0;
        accum_y = 0;
        accum_z = 0;

        packets_sent++;

        if (debug_enabled) {
            printf("PS2MOUSE: Sent packet (type=%d)\n", mouse_type);
        }
    }

    // Process command from host
    void receiveCommand(uint8_t cmd) {
        commands_received++;

        if (wrap_mode && cmd != CMD_RESET && cmd != CMD_RESET_WRAP_MODE) {
            // Echo back in wrap mode
            queueByte(cmd);
            return;
        }

        if (waiting_for_param) {
            handleParameter(cmd);
            return;
        }

        if (debug_enabled) {
            printf("PS2MOUSE: Received command 0x%02X\n", cmd);
        }

        switch (cmd) {
            case CMD_RESET:
                queueByte(RESP_ACK);
                // Soft reset - don't clear buffer, just send BAT and ID
                mouse_type = MOUSE_STANDARD;
                enabled = false;
                stream_mode = true;
                wrap_mode = false;
                sample_rate = 100;
                resolution = RES_4_COUNT;
                scaling_2_1 = false;
                button_state = 0;
                accum_x = accum_y = accum_z = 0;
                intellimouse_seq = 0;
                queueByte(RESP_BAT_OK);
                queueByte(mouse_type);
                break;

            case CMD_RESEND:
                queueByte(RESP_ACK);
                break;

            case CMD_SET_DEFAULTS:
                queueByte(RESP_ACK);
                enabled = false;
                stream_mode = true;
                sample_rate = 100;
                resolution = RES_4_COUNT;
                scaling_2_1 = false;
                break;

            case CMD_DISABLE_REPORTING:
                queueByte(RESP_ACK);
                enabled = false;
                break;

            case CMD_ENABLE_REPORTING:
                queueByte(RESP_ACK);
                enabled = true;
                break;

            case CMD_SET_SAMPLE_RATE:
                queueByte(RESP_ACK);
                waiting_for_param = true;
                pending_command = cmd;
                break;

            case CMD_GET_DEVICE_ID:
                queueByte(RESP_ACK);
                queueByte(mouse_type);
                break;

            case CMD_SET_REMOTE_MODE:
                queueByte(RESP_ACK);
                stream_mode = false;
                break;

            case CMD_SET_WRAP_MODE:
                queueByte(RESP_ACK);
                wrap_mode = true;
                break;

            case CMD_RESET_WRAP_MODE:
                queueByte(RESP_ACK);
                wrap_mode = false;
                break;

            case CMD_READ_DATA:
                queueByte(RESP_ACK);
                sendDataPacket();
                break;

            case CMD_SET_STREAM_MODE:
                queueByte(RESP_ACK);
                stream_mode = true;
                break;

            case CMD_STATUS_REQUEST:
                queueByte(RESP_ACK);
                sendStatusPacket();
                break;

            case CMD_SET_RESOLUTION:
                queueByte(RESP_ACK);
                waiting_for_param = true;
                pending_command = cmd;
                break;

            case CMD_SET_SCALING_2_1:
                queueByte(RESP_ACK);
                scaling_2_1 = true;
                break;

            case CMD_SET_SCALING_1_1:
                queueByte(RESP_ACK);
                scaling_2_1 = false;
                break;

            default:
                queueByte(RESP_ACK);
                break;
        }
    }

    // Get next byte to send
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

    // State accessors
    bool isEnabled() const { return enabled; }
    bool isStreamMode() const { return stream_mode; }
    MouseType getMouseType() const { return mouse_type; }
    uint8_t getButtonState() const { return button_state; }
    uint8_t getSampleRate() const { return sample_rate; }
    uint8_t getResolution() const { return resolution; }

    // Statistics
    uint32_t getPacketsSent() const { return packets_sent; }
    uint32_t getCommandsReceived() const { return commands_received; }

    void printStats() const {
        printf("PS/2 Mouse Statistics:\n");
        printf("  Type:          %s\n",
               mouse_type == MOUSE_STANDARD ? "Standard" :
               mouse_type == MOUSE_WHEEL ? "Wheel" : "5-Button");
        printf("  Packets sent:  %u\n", packets_sent);
        printf("  Commands:      %u\n", commands_received);
        printf("  Sample rate:   %u\n", sample_rate);
        printf("  Resolution:    %u\n", resolution);
        printf("  Enabled:       %s\n", enabled ? "Yes" : "No");
    }

    // Direct packet injection (for testing)
    void injectByte(uint8_t byte) {
        queueByte(byte);
    }

    // Force mouse type (for testing)
    void setMouseType(MouseType type) {
        mouse_type = type;
    }

private:
    void queueByte(uint8_t byte) {
        output_buffer.push(byte);
    }

    void handleParameter(uint8_t param) {
        waiting_for_param = false;

        switch (pending_command) {
            case CMD_SET_SAMPLE_RATE:
                sample_rate = param;
                queueByte(RESP_ACK);

                // Check for Intellimouse detection sequence
                checkIntellimouseSequence(param);
                break;

            case CMD_SET_RESOLUTION:
                if (param <= 3) {
                    resolution = param;
                    queueByte(RESP_ACK);
                } else {
                    queueByte(RESP_ERROR);
                }
                break;

            default:
                queueByte(RESP_ACK);
                break;
        }
    }

    void checkIntellimouseSequence(uint8_t rate) {
        // Intellimouse wheel detection: 200, 100, 80
        // 5-button detection: 200, 200, 80
        if (intellimouse_seq == 0 && rate == 200) {
            intellimouse_seq = 1;
        } else if (intellimouse_seq == 1 && rate == 100) {
            intellimouse_seq = 2;
        } else if (intellimouse_seq == 1 && rate == 200) {
            intellimouse_seq = 10;  // 5-button path
        } else if (intellimouse_seq == 2 && rate == 80) {
            // Wheel mouse detected
            mouse_type = MOUSE_WHEEL;
            intellimouse_seq = 0;
            if (debug_enabled) {
                printf("PS2MOUSE: Intellimouse wheel detected\n");
            }
        } else if (intellimouse_seq == 10 && rate == 80) {
            // 5-button mouse detected
            mouse_type = MOUSE_5BUTTON;
            intellimouse_seq = 0;
            if (debug_enabled) {
                printf("PS2MOUSE: Intellimouse 5-button detected\n");
            }
        } else {
            intellimouse_seq = 0;
        }
    }

    void sendDataPacket() {
        // Send current state as packet (for remote mode)
        uint8_t byte1 = 0x08;
        byte1 |= (button_state & BTN_LEFT) ? 0x01 : 0;
        byte1 |= (button_state & BTN_RIGHT) ? 0x02 : 0;
        byte1 |= (button_state & BTN_MIDDLE) ? 0x04 : 0;

        int8_t dx = (accum_x > 127) ? 127 : ((accum_x < -128) ? -128 : accum_x);
        int8_t dy = (accum_y > 127) ? 127 : ((accum_y < -128) ? -128 : accum_y);

        if (dx < 0) byte1 |= 0x10;
        if (dy < 0) byte1 |= 0x20;

        queueByte(byte1);
        queueByte((uint8_t)dx);
        queueByte((uint8_t)dy);

        if (mouse_type != MOUSE_STANDARD) {
            uint8_t byte4 = accum_z & 0x0F;
            if (mouse_type == MOUSE_5BUTTON) {
                if (button_state & BTN_4) byte4 |= 0x10;
                if (button_state & BTN_5) byte4 |= 0x20;
            }
            queueByte(byte4);
        }

        accum_x = accum_y = accum_z = 0;
        packets_sent++;
    }

    void sendStatusPacket() {
        // Status packet format:
        // Byte 1: 0 0 Remote Enable Scaling 0 LB MB RB
        // Byte 2: Resolution
        // Byte 3: Sample rate
        uint8_t byte1 = 0;
        if (!stream_mode) byte1 |= 0x40;
        if (enabled) byte1 |= 0x20;
        if (scaling_2_1) byte1 |= 0x10;
        byte1 |= (button_state & BTN_LEFT) ? 0x04 : 0;
        byte1 |= (button_state & BTN_MIDDLE) ? 0x02 : 0;
        byte1 |= (button_state & BTN_RIGHT) ? 0x01 : 0;

        queueByte(byte1);
        queueByte(resolution);
        queueByte(sample_rate);
    }

    int16_t applyScaling(int16_t value) {
        // 2:1 scaling table
        int16_t abs_val = (value < 0) ? -value : value;
        int16_t scaled;

        if (abs_val <= 1) scaled = abs_val;
        else if (abs_val == 2) scaled = 1;
        else if (abs_val == 3) scaled = 3;
        else if (abs_val == 4) scaled = 6;
        else if (abs_val == 5) scaled = 9;
        else scaled = abs_val * 2;

        return (value < 0) ? -scaled : scaled;
    }
};

#endif // PS2_MOUSE_MODEL_CPP_H
