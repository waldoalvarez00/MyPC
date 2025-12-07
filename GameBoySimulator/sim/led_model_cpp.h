// MiSTer LED Model for Verilator Simulation
// Supports MiSTer LED outputs and software-controlled LED register
//
// Features:
// - MiSTer LED outputs (USER, POWER, DISK)
// - 16-bit LED register for software control
// - LED patterns (blink, pulse, activity indication)
// - State history and transition tracking
// - PWM brightness support

#ifndef LED_MODEL_CPP_H
#define LED_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

class LEDModelCpp {
public:
    // MiSTer LED types
    enum LEDType {
        LED_TYPE_USER,      // Single bit LED
        LED_TYPE_POWER,     // 2-bit with control mode
        LED_TYPE_DISK,      // 2-bit with control mode
        LED_TYPE_ACCENT,    // RGB accent LED
        LED_TYPE_REGISTER   // Software register LED
    };

    // LED patterns
    enum LEDPattern {
        PATTERN_SOLID,      // Always on
        PATTERN_BLINK_SLOW, // 1 Hz blink
        PATTERN_BLINK_FAST, // 4 Hz blink
        PATTERN_PULSE,      // PWM fade in/out
        PATTERN_ACTIVITY,   // Brief flash on activity
        PATTERN_HEARTBEAT   // Double-blink heartbeat
    };

    // LED control modes (for POWER/DISK)
    enum LEDControlMode {
        CONTROL_SYSTEM = 0,  // System controls LED
        CONTROL_USER = 1     // User controls LED directly
    };

private:
    // MiSTer LED states
    bool led_user;
    uint8_t led_power;      // [1:0] - bit 1 = mode, bit 0 = state
    uint8_t led_disk;       // [1:0] - bit 1 = mode, bit 0 = state

    // Software LED register (16 bits)
    uint16_t led_register;

    // Pattern state
    LEDPattern current_pattern;
    uint32_t pattern_counter;
    uint32_t pattern_period;

    // Activity tracking
    bool activity_pending;
    uint32_t activity_counter;
    uint32_t activity_duration;

    // PWM/brightness
    uint8_t pwm_counter;
    uint8_t brightness;

    // History tracking
    struct LEDEvent {
        uint64_t timestamp;
        uint8_t led_id;
        bool state;
    };
    std::vector<LEDEvent> history;
    uint64_t current_time;

    // Statistics
    uint32_t user_toggles;
    uint32_t power_toggles;
    uint32_t disk_toggles;
    uint32_t register_writes;
    uint64_t user_on_time;
    uint64_t power_on_time;
    uint64_t disk_on_time;

    // Debug
    bool debug_enabled;

public:
    LEDModelCpp(bool debug = false)
        : debug_enabled(debug) {
        reset();
    }

    void reset() {
        led_user = false;
        led_power = 0;
        led_disk = 0;
        led_register = 0;

        current_pattern = PATTERN_SOLID;
        pattern_counter = 0;
        pattern_period = 50000;  // Default 1 Hz at 50 MHz

        activity_pending = false;
        activity_counter = 0;
        activity_duration = 5000;  // 100us at 50 MHz

        pwm_counter = 0;
        brightness = 255;

        history.clear();
        current_time = 0;

        user_toggles = 0;
        power_toggles = 0;
        disk_toggles = 0;
        register_writes = 0;
        user_on_time = 0;
        power_on_time = 0;
        disk_on_time = 0;

        if (debug_enabled) {
            printf("LED: Reset complete\n");
        }
    }

    // Update LED states (call each clock cycle)
    void update() {
        current_time++;

        // Track on-time
        if (led_user) user_on_time++;
        if (getPowerState()) power_on_time++;
        if (getDiskState()) disk_on_time++;

        // Update pattern counter
        pattern_counter++;
        if (pattern_counter >= pattern_period) {
            pattern_counter = 0;
        }

        // Update activity counter
        if (activity_pending) {
            activity_counter++;
            if (activity_counter >= activity_duration) {
                activity_pending = false;
                activity_counter = 0;
            }
        }

        // Update PWM counter
        pwm_counter++;
    }

    // Set USER LED
    void setUserLED(bool state) {
        if (led_user != state) {
            led_user = state;
            user_toggles++;
            recordEvent(0, state);

            if (debug_enabled) {
                printf("LED: USER = %d\n", state);
            }
        }
    }

    // Set POWER LED (2-bit)
    void setPowerLED(uint8_t value) {
        if (led_power != (value & 0x03)) {
            bool old_state = getPowerState();
            led_power = value & 0x03;
            bool new_state = getPowerState();

            if (old_state != new_state) {
                power_toggles++;
                recordEvent(1, new_state);
            }

            if (debug_enabled) {
                printf("LED: POWER = 0x%02X (mode=%d, state=%d)\n",
                       led_power, (led_power >> 1) & 1, led_power & 1);
            }
        }
    }

    // Set DISK LED (2-bit)
    void setDiskLED(uint8_t value) {
        if (led_disk != (value & 0x03)) {
            bool old_state = getDiskState();
            led_disk = value & 0x03;
            bool new_state = getDiskState();

            if (old_state != new_state) {
                disk_toggles++;
                recordEvent(2, new_state);
            }

            if (debug_enabled) {
                printf("LED: DISK = 0x%02X (mode=%d, state=%d)\n",
                       led_disk, (led_disk >> 1) & 1, led_disk & 1);
            }
        }
    }

    // Set LED register (16-bit)
    void setRegister(uint16_t value) {
        if (led_register != value) {
            led_register = value;
            register_writes++;

            if (debug_enabled) {
                printf("LED: Register = 0x%04X\n", led_register);
            }
        }
    }

    // Set individual register bit
    void setRegisterBit(int bit, bool state) {
        if (bit < 0 || bit > 15) return;

        uint16_t mask = 1 << bit;
        uint16_t new_value = state ? (led_register | mask) : (led_register & ~mask);
        setRegister(new_value);
    }

    // Trigger activity indication
    void triggerActivity() {
        activity_pending = true;
        activity_counter = 0;

        if (debug_enabled) {
            printf("LED: Activity triggered\n");
        }
    }

    // Set pattern
    void setPattern(LEDPattern pattern) {
        current_pattern = pattern;
        pattern_counter = 0;

        // Set period based on pattern
        switch (pattern) {
            case PATTERN_BLINK_SLOW: pattern_period = 25000000; break;  // 0.5 sec
            case PATTERN_BLINK_FAST: pattern_period = 6250000; break;   // 0.125 sec
            case PATTERN_PULSE:      pattern_period = 12500000; break;  // 0.25 sec
            case PATTERN_HEARTBEAT:  pattern_period = 50000000; break;  // 1 sec
            default:                 pattern_period = 50000000; break;
        }
    }

    // Set brightness (0-255)
    void setBrightness(uint8_t level) {
        brightness = level;
    }

    // Get LED states
    bool getUserLED() const { return led_user; }

    bool getPowerState() const {
        // If mode bit (bit 1) is set, use user control (bit 0)
        // Otherwise, could incorporate system status
        return (led_power & 0x01) != 0;
    }

    bool getDiskState() const {
        return (led_disk & 0x01) != 0;
    }

    uint8_t getPowerRaw() const { return led_power; }
    uint8_t getDiskRaw() const { return led_disk; }
    uint16_t getRegister() const { return led_register; }

    bool getRegisterBit(int bit) const {
        if (bit < 0 || bit > 15) return false;
        return (led_register & (1 << bit)) != 0;
    }

    // Get pattern-modified state
    bool getPatternState() const {
        switch (current_pattern) {
            case PATTERN_SOLID:
                return true;

            case PATTERN_BLINK_SLOW:
            case PATTERN_BLINK_FAST:
                return pattern_counter < (pattern_period / 2);

            case PATTERN_PULSE: {
                // Triangle wave
                uint32_t half = pattern_period / 2;
                uint32_t level = (pattern_counter < half) ?
                    pattern_counter : (pattern_period - pattern_counter);
                return (level * 255 / half) > 127;
            }

            case PATTERN_ACTIVITY:
                return activity_pending;

            case PATTERN_HEARTBEAT: {
                // Double blink pattern
                uint32_t phase = pattern_counter * 8 / pattern_period;
                return (phase == 0 || phase == 2);
            }

            default:
                return true;
        }
    }

    // Get PWM output for brightness
    bool getPWMOutput() const {
        return pwm_counter < brightness;
    }

    // Check if activity is active
    bool isActivityActive() const {
        return activity_pending;
    }

    // Get history
    const std::vector<LEDEvent>& getHistory() const {
        return history;
    }

    // Get statistics
    uint32_t getUserToggles() const { return user_toggles; }
    uint32_t getPowerToggles() const { return power_toggles; }
    uint32_t getDiskToggles() const { return disk_toggles; }
    uint32_t getRegisterWrites() const { return register_writes; }
    uint64_t getUserOnTime() const { return user_on_time; }
    uint64_t getPowerOnTime() const { return power_on_time; }
    uint64_t getDiskOnTime() const { return disk_on_time; }

    // Calculate duty cycle (percentage)
    float getUserDutyCycle() const {
        if (current_time == 0) return 0.0f;
        return (float)user_on_time * 100.0f / (float)current_time;
    }

    float getPowerDutyCycle() const {
        if (current_time == 0) return 0.0f;
        return (float)power_on_time * 100.0f / (float)current_time;
    }

    float getDiskDutyCycle() const {
        if (current_time == 0) return 0.0f;
        return (float)disk_on_time * 100.0f / (float)current_time;
    }

    void printStats() const {
        printf("LED Statistics:\n");
        printf("  USER LED:   %d toggles, %.1f%% duty cycle\n",
               user_toggles, getUserDutyCycle());
        printf("  POWER LED:  %d toggles, %.1f%% duty cycle\n",
               power_toggles, getPowerDutyCycle());
        printf("  DISK LED:   %d toggles, %.1f%% duty cycle\n",
               disk_toggles, getDiskDutyCycle());
        printf("  Register:   %d writes, current=0x%04X\n",
               register_writes, led_register);
        printf("  History:    %zu events\n", history.size());
    }

    void printRegisterBits() const {
        printf("LED Register: ");
        for (int i = 15; i >= 0; i--) {
            printf("%c", getRegisterBit(i) ? '1' : '0');
            if (i == 8) printf(" ");
        }
        printf(" (0x%04X)\n", led_register);
    }

private:
    void recordEvent(uint8_t led_id, bool state) {
        LEDEvent event;
        event.timestamp = current_time;
        event.led_id = led_id;
        event.state = state;
        history.push_back(event);

        // Limit history size
        if (history.size() > 1000) {
            history.erase(history.begin());
        }
    }
};

#endif // LED_MODEL_CPP_H
