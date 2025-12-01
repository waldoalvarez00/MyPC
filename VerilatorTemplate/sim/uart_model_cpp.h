// UART Model for Verilator Simulation
// 16550/16750 compatible serial port model
//
// Features:
// - TX/RX with configurable FIFO (16/64 bytes)
// - Baud rate divisor
// - Data bits (5-8), parity, stop bits
// - Modem control signals (RTS, CTS, DTR, DSR, DCD, RI)
// - Line status with error detection
// - Interrupt generation
// - Loopback mode

#ifndef UART_MODEL_CPP_H
#define UART_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <queue>

class UARTModelCpp {
public:
    // Register offsets (DLAB=0)
    enum Register {
        REG_RBR = 0,    // Receive Buffer Register (read)
        REG_THR = 0,    // Transmit Holding Register (write)
        REG_IER = 1,    // Interrupt Enable Register
        REG_IIR = 2,    // Interrupt Identification Register (read)
        REG_FCR = 2,    // FIFO Control Register (write)
        REG_LCR = 3,    // Line Control Register
        REG_MCR = 4,    // Modem Control Register
        REG_LSR = 5,    // Line Status Register
        REG_MSR = 6,    // Modem Status Register
        REG_SCR = 7,    // Scratch Register
        // DLAB=1
        REG_DLL = 0,    // Divisor Latch Low
        REG_DLM = 1     // Divisor Latch High
    };

    // Line Control Register bits
    enum LCRBits {
        LCR_WLS0  = 0x01,   // Word length bit 0
        LCR_WLS1  = 0x02,   // Word length bit 1
        LCR_STB   = 0x04,   // Stop bits
        LCR_PEN   = 0x08,   // Parity enable
        LCR_EPS   = 0x10,   // Even parity select
        LCR_SP    = 0x20,   // Stick parity
        LCR_BC    = 0x40,   // Break control
        LCR_DLAB  = 0x80    // Divisor latch access bit
    };

    // Line Status Register bits
    enum LSRBits {
        LSR_DR   = 0x01,    // Data ready
        LSR_OE   = 0x02,    // Overrun error
        LSR_PE   = 0x04,    // Parity error
        LSR_FE   = 0x08,    // Framing error
        LSR_BI   = 0x10,    // Break interrupt
        LSR_THRE = 0x20,    // THR empty
        LSR_TEMT = 0x40,    // Transmitter empty
        LSR_RXFE = 0x80     // RX FIFO error
    };

    // Modem Control Register bits
    enum MCRBits {
        MCR_DTR  = 0x01,    // Data Terminal Ready
        MCR_RTS  = 0x02,    // Request to Send
        MCR_OUT1 = 0x04,    // Output 1
        MCR_OUT2 = 0x08,    // Output 2 (interrupt enable)
        MCR_LOOP = 0x10     // Loopback mode
    };

    // Modem Status Register bits
    enum MSRBits {
        MSR_DCTS = 0x01,    // Delta CTS
        MSR_DDSR = 0x02,    // Delta DSR
        MSR_TERI = 0x04,    // Trailing edge RI
        MSR_DDCD = 0x08,    // Delta DCD
        MSR_CTS  = 0x10,    // CTS
        MSR_DSR  = 0x20,    // DSR
        MSR_RI   = 0x40,    // Ring Indicator
        MSR_DCD  = 0x80     // Data Carrier Detect
    };

    // Interrupt Enable Register bits
    enum IERBits {
        IER_ERBFI = 0x01,   // Enable RX data available
        IER_ETBEI = 0x02,   // Enable THR empty
        IER_ELSI  = 0x04,   // Enable line status
        IER_EDSSI = 0x08    // Enable modem status
    };

    // Interrupt types
    enum InterruptType {
        INT_NONE   = 0x01,  // No interrupt
        INT_RLS    = 0x06,  // Receiver line status
        INT_RDA    = 0x04,  // Receiver data available
        INT_CTI    = 0x0C,  // Character timeout
        INT_THRE   = 0x02,  // THR empty
        INT_MSI    = 0x00   // Modem status
    };

private:
    // Registers
    uint8_t ier;        // Interrupt Enable
    uint8_t lcr;        // Line Control
    uint8_t mcr;        // Modem Control
    uint8_t lsr;        // Line Status
    uint8_t msr;        // Modem Status
    uint8_t scr;        // Scratch
    uint16_t divisor;   // Baud rate divisor

    // FIFO
    std::queue<uint8_t> rx_fifo;
    std::queue<uint8_t> tx_fifo;
    bool fifo_enabled;
    int fifo_size;      // 16 or 64
    int rx_trigger;     // FIFO trigger level

    // TX state
    bool tx_shift_empty;
    uint8_t tx_shift;

    // Modem input signals
    bool cts_in;
    bool dsr_in;
    bool dcd_in;
    bool ri_in;

    // Statistics
    uint32_t bytes_tx;
    uint32_t bytes_rx;
    uint32_t overrun_errors;
    uint32_t parity_errors;
    uint32_t framing_errors;

    // Debug
    bool debug_enabled;

public:
    UARTModelCpp(bool debug = false)
        : debug_enabled(debug) {
        reset();
    }

    void reset() {
        ier = 0x00;
        lcr = 0x00;
        mcr = 0x00;
        lsr = LSR_THRE | LSR_TEMT;
        msr = 0x00;
        scr = 0x00;
        divisor = 1;

        while (!rx_fifo.empty()) rx_fifo.pop();
        while (!tx_fifo.empty()) tx_fifo.pop();
        fifo_enabled = false;
        fifo_size = 16;
        rx_trigger = 1;

        tx_shift_empty = true;
        tx_shift = 0;

        cts_in = true;
        dsr_in = true;
        dcd_in = false;
        ri_in = false;

        bytes_tx = 0;
        bytes_rx = 0;
        overrun_errors = 0;
        parity_errors = 0;
        framing_errors = 0;

        updateMSR();

        if (debug_enabled) {
            printf("UART: Reset complete\n");
        }
    }

    // Register write
    void writeReg(uint8_t addr, uint8_t data) {
        addr &= 0x07;

        // Check DLAB for register select
        if (lcr & LCR_DLAB) {
            if (addr == REG_DLL) {
                divisor = (divisor & 0xFF00) | data;
                if (debug_enabled) {
                    printf("UART: DLL = 0x%02X (divisor=%d)\n", data, divisor);
                }
                return;
            } else if (addr == REG_DLM) {
                divisor = (divisor & 0x00FF) | ((uint16_t)data << 8);
                if (debug_enabled) {
                    printf("UART: DLM = 0x%02X (divisor=%d)\n", data, divisor);
                }
                return;
            }
        }

        switch (addr) {
            case REG_THR:
                writeTHR(data);
                break;

            case REG_IER:
                ier = data & 0x0F;
                if (debug_enabled) {
                    printf("UART: IER = 0x%02X\n", ier);
                }
                break;

            case REG_FCR:
                writeFCR(data);
                break;

            case REG_LCR:
                lcr = data;
                if (debug_enabled) {
                    printf("UART: LCR = 0x%02X (%d%c%s)\n", lcr,
                           5 + (lcr & 0x03),
                           (lcr & LCR_PEN) ? ((lcr & LCR_EPS) ? 'E' : 'O') : 'N',
                           (lcr & LCR_STB) ? "2" : "1");
                }
                break;

            case REG_MCR:
                mcr = data & 0x1F;
                if (debug_enabled) {
                    printf("UART: MCR = 0x%02X (DTR=%d RTS=%d LOOP=%d)\n",
                           mcr, (mcr & MCR_DTR) != 0, (mcr & MCR_RTS) != 0,
                           (mcr & MCR_LOOP) != 0);
                }
                // Update MSR for loopback
                if (mcr & MCR_LOOP) {
                    updateMSR();
                }
                break;

            case REG_SCR:
                scr = data;
                break;

            default:
                break;
        }
    }

    // Register read
    uint8_t readReg(uint8_t addr) {
        addr &= 0x07;

        // Check DLAB for register select
        if (lcr & LCR_DLAB) {
            if (addr == REG_DLL) return divisor & 0xFF;
            if (addr == REG_DLM) return (divisor >> 8) & 0xFF;
        }

        switch (addr) {
            case REG_RBR:
                return readRBR();

            case REG_IER:
                return ier;

            case REG_IIR:
                return getIIR();

            case REG_LCR:
                return lcr;

            case REG_MCR:
                return mcr;

            case REG_LSR:
                return readLSR();

            case REG_MSR:
                return readMSR();

            case REG_SCR:
                return scr;

            default:
                return 0xFF;
        }
    }

    // External receive (data coming into UART)
    void receive(uint8_t data) {
        if (mcr & MCR_LOOP) {
            // In loopback, ignore external data
            return;
        }

        if (fifo_enabled) {
            if ((int)rx_fifo.size() >= fifo_size) {
                lsr |= LSR_OE;
                overrun_errors++;
            } else {
                rx_fifo.push(data);
            }
        } else {
            if (lsr & LSR_DR) {
                lsr |= LSR_OE;
                overrun_errors++;
            } else {
                rx_fifo.push(data);
            }
        }

        lsr |= LSR_DR;
        bytes_rx++;

        if (debug_enabled) {
            printf("UART: Received 0x%02X '%c'\n", data,
                   (data >= 32 && data < 127) ? data : '.');
        }
    }

    // Get transmitted data (data going out of UART)
    bool getTransmit(uint8_t& data) {
        if (tx_fifo.empty()) {
            return false;
        }

        data = tx_fifo.front();
        tx_fifo.pop();

        // Update LSR
        if (tx_fifo.empty()) {
            lsr |= LSR_THRE | LSR_TEMT;
        }

        bytes_tx++;

        if (debug_enabled) {
            printf("UART: Transmit 0x%02X '%c'\n", data,
                   (data >= 32 && data < 127) ? data : '.');
        }

        return true;
    }

    // Check if data ready to transmit
    bool hasTxData() const {
        return !tx_fifo.empty();
    }

    // Check if RX data available
    bool hasRxData() const {
        return !rx_fifo.empty();
    }

    // Set modem input signals
    void setCTS(bool state) {
        if (cts_in != state) {
            cts_in = state;
            updateMSR();
        }
    }

    void setDSR(bool state) {
        if (dsr_in != state) {
            dsr_in = state;
            updateMSR();
        }
    }

    void setDCD(bool state) {
        if (dcd_in != state) {
            dcd_in = state;
            updateMSR();
        }
    }

    void setRI(bool state) {
        if (ri_in && !state) {
            // Trailing edge
            msr |= MSR_TERI;
        }
        ri_in = state;
        updateMSR();
    }

    // Get modem output signals
    bool getDTR() const { return (mcr & MCR_DTR) != 0; }
    bool getRTS() const { return (mcr & MCR_RTS) != 0; }
    bool getOUT1() const { return (mcr & MCR_OUT1) != 0; }
    bool getOUT2() const { return (mcr & MCR_OUT2) != 0; }

    // Check for interrupt
    bool hasInterrupt() const {
        if (!(mcr & MCR_OUT2)) return false;  // OUT2 gates interrupts

        uint8_t iir = getIIR();
        return (iir & 0x01) == 0;  // Bit 0 = 0 means interrupt pending
    }

    // Get configuration
    int getDataBits() const { return 5 + (lcr & 0x03); }
    int getStopBits() const { return (lcr & LCR_STB) ? 2 : 1; }
    char getParity() const {
        if (!(lcr & LCR_PEN)) return 'N';
        if (lcr & LCR_SP) return (lcr & LCR_EPS) ? 'L' : 'H';  // Stick
        return (lcr & LCR_EPS) ? 'E' : 'O';
    }
    uint16_t getDivisor() const { return divisor; }
    bool isLoopback() const { return (mcr & MCR_LOOP) != 0; }
    bool isFifoEnabled() const { return fifo_enabled; }

    // Statistics
    uint32_t getBytesTX() const { return bytes_tx; }
    uint32_t getBytesRX() const { return bytes_rx; }
    uint32_t getOverrunErrors() const { return overrun_errors; }
    uint32_t getParityErrors() const { return parity_errors; }
    uint32_t getFramingErrors() const { return framing_errors; }

    void printStats() const {
        printf("UART Statistics:\n");
        printf("  TX bytes:       %u\n", bytes_tx);
        printf("  RX bytes:       %u\n", bytes_rx);
        printf("  Config:         %d%c%d\n", getDataBits(), getParity(), getStopBits());
        printf("  Divisor:        %d\n", divisor);
        printf("  FIFO:           %s (%d bytes)\n",
               fifo_enabled ? "enabled" : "disabled", fifo_size);
        printf("  Overrun errors: %u\n", overrun_errors);
        printf("  Parity errors:  %u\n", parity_errors);
        printf("  Framing errors: %u\n", framing_errors);
    }

private:
    void writeTHR(uint8_t data) {
        if (mcr & MCR_LOOP) {
            // Loopback - data goes directly to RX
            receive(data);
        } else {
            tx_fifo.push(data);
        }

        lsr &= ~(LSR_THRE | LSR_TEMT);

        if (debug_enabled) {
            printf("UART: THR = 0x%02X '%c'\n", data,
                   (data >= 32 && data < 127) ? data : '.');
        }
    }

    void writeFCR(uint8_t data) {
        fifo_enabled = (data & 0x01) != 0;

        if (data & 0x02) {
            // Clear RX FIFO
            while (!rx_fifo.empty()) rx_fifo.pop();
            lsr &= ~LSR_DR;
        }

        if (data & 0x04) {
            // Clear TX FIFO
            while (!tx_fifo.empty()) tx_fifo.pop();
            lsr |= LSR_THRE | LSR_TEMT;
        }

        // FIFO trigger level
        switch ((data >> 6) & 0x03) {
            case 0: rx_trigger = 1; break;
            case 1: rx_trigger = 4; break;
            case 2: rx_trigger = 8; break;
            case 3: rx_trigger = 14; break;
        }

        // 64-byte FIFO (16750)
        if (data & 0x20) {
            fifo_size = 64;
        } else {
            fifo_size = 16;
        }

        if (debug_enabled) {
            printf("UART: FCR = 0x%02X (FIFO=%s, trigger=%d, size=%d)\n",
                   data, fifo_enabled ? "on" : "off", rx_trigger, fifo_size);
        }
    }

    uint8_t readRBR() {
        if (rx_fifo.empty()) {
            return 0;
        }

        uint8_t data = rx_fifo.front();
        rx_fifo.pop();

        if (rx_fifo.empty()) {
            lsr &= ~LSR_DR;
        }

        return data;
    }

    uint8_t readLSR() {
        uint8_t result = lsr;
        // Clear error bits on read
        lsr &= ~(LSR_OE | LSR_PE | LSR_FE | LSR_BI | LSR_RXFE);
        return result;
    }

    uint8_t readMSR() {
        uint8_t result = msr;
        // Clear delta bits on read
        msr &= ~(MSR_DCTS | MSR_DDSR | MSR_TERI | MSR_DDCD);
        return result;
    }

    uint8_t getIIR() const {
        // Check interrupt sources in priority order
        if ((ier & IER_ELSI) && (lsr & (LSR_OE | LSR_PE | LSR_FE | LSR_BI))) {
            return INT_RLS | (fifo_enabled ? 0xC0 : 0);
        }

        if ((ier & IER_ERBFI) && (lsr & LSR_DR)) {
            if (fifo_enabled && (int)rx_fifo.size() >= rx_trigger) {
                return INT_RDA | (fifo_enabled ? 0xC0 : 0);
            } else if (!fifo_enabled) {
                return INT_RDA;
            }
        }

        if ((ier & IER_ETBEI) && (lsr & LSR_THRE)) {
            return INT_THRE | (fifo_enabled ? 0xC0 : 0);
        }

        if ((ier & IER_EDSSI) && (msr & 0x0F)) {
            return INT_MSI | (fifo_enabled ? 0xC0 : 0);
        }

        return INT_NONE | (fifo_enabled ? 0xC0 : 0);
    }

    void updateMSR() {
        uint8_t old_msr = msr & 0xF0;
        uint8_t new_msr = 0;

        if (mcr & MCR_LOOP) {
            // Loopback - connect outputs to inputs
            if (mcr & MCR_RTS) new_msr |= MSR_CTS;
            if (mcr & MCR_DTR) new_msr |= MSR_DSR;
            if (mcr & MCR_OUT1) new_msr |= MSR_RI;
            if (mcr & MCR_OUT2) new_msr |= MSR_DCD;
        } else {
            if (cts_in) new_msr |= MSR_CTS;
            if (dsr_in) new_msr |= MSR_DSR;
            if (ri_in) new_msr |= MSR_RI;
            if (dcd_in) new_msr |= MSR_DCD;
        }

        // Set delta bits
        if ((old_msr ^ new_msr) & MSR_CTS) msr |= MSR_DCTS;
        if ((old_msr ^ new_msr) & MSR_DSR) msr |= MSR_DDSR;
        if ((old_msr ^ new_msr) & MSR_DCD) msr |= MSR_DDCD;

        msr = (msr & 0x0F) | new_msr;
    }
};

#endif // UART_MODEL_CPP_H
