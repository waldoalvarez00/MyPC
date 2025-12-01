// Floppy Disk Model for Verilator Simulation
// Supports PC-style floppy disk operations with multiple formats
//
// Features:
// - Multiple disk formats (360K, 720K, 1.2M, 1.44M, 2.88M)
// - Read/write/format/seek operations
// - Disk image file loading (IMG, IMA, VFD, ADF)
// - Track geometry and CHS addressing
// - Write protection support
// - Optional timing simulation

#ifndef FLOPPY_MODEL_CPP_H
#define FLOPPY_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <string>
#include <fstream>

class FloppyModelCpp {
public:
    // Disk formats
    enum DiskFormat {
        FMT_NONE = 0,
        FMT_160K,    // 5.25" SS/DD (160K)
        FMT_180K,    // 5.25" SS/DD (180K)
        FMT_320K,    // 5.25" DS/DD (320K)
        FMT_360K,    // 5.25" DS/DD (360K)
        FMT_720K,    // 3.5"  DS/DD (720K)
        FMT_1200K,   // 5.25" DS/HD (1.2M)
        FMT_1440K,   // 3.5"  DS/HD (1.44M)
        FMT_2880K,   // 3.5"  DS/ED (2.88M)
        FMT_AMIGA_DD, // Amiga DD (880K)
        FMT_AMIGA_HD  // Amiga HD (1.76M)
    };

    // Disk geometry structure
    struct DiskGeometry {
        uint16_t cylinders;
        uint8_t heads;
        uint8_t sectors_per_track;
        uint16_t bytes_per_sector;
        uint32_t total_sectors;
        uint32_t total_size;
        const char* name;
    };

    // Sector address (CHS)
    struct CHSAddress {
        uint8_t cylinder;
        uint8_t head;
        uint8_t sector;
    };

    // Operation status
    enum OpStatus {
        OP_SUCCESS = 0,
        OP_NO_DISK,
        OP_SEEK_ERROR,
        OP_CRC_ERROR,
        OP_NOT_FOUND,
        OP_WRITE_PROTECT,
        OP_BAD_SECTOR,
        OP_END_OF_TRACK,
        OP_FORMAT_ERROR
    };

    // Standard disk geometries
    static constexpr DiskGeometry GEOMETRIES[] = {
        {0, 0, 0, 0, 0, 0, "No Disk"},
        {40, 1, 8, 512, 320, 163840, "160K"},
        {40, 1, 9, 512, 360, 184320, "180K"},
        {40, 2, 8, 512, 640, 327680, "320K"},
        {40, 2, 9, 512, 720, 368640, "360K"},
        {80, 2, 9, 512, 1440, 737280, "720K"},
        {80, 2, 15, 512, 2400, 1228800, "1.2M"},
        {80, 2, 18, 512, 2880, 1474560, "1.44M"},
        {80, 2, 36, 512, 5760, 2949120, "2.88M"},
        {80, 2, 11, 512, 1760, 901120, "Amiga DD"},
        {80, 2, 22, 512, 3520, 1802240, "Amiga HD"}
    };

private:
    // Disk data
    std::vector<uint8_t> disk_data;
    DiskFormat format;
    DiskGeometry geometry;
    std::string image_filename;

    // Drive state
    uint8_t current_cylinder;
    uint8_t current_head;
    bool disk_inserted;
    bool write_protected;
    bool motor_on;
    bool disk_changed;

    // Statistics
    uint32_t read_count;
    uint32_t write_count;
    uint32_t seek_count;
    uint32_t format_count;
    uint32_t error_count;

    // Debug
    bool debug_enabled;

public:
    FloppyModelCpp(bool debug = false)
        : debug_enabled(debug) {
        reset();
    }

    void reset() {
        disk_data.clear();
        format = FMT_NONE;
        geometry = GEOMETRIES[0];
        image_filename.clear();

        current_cylinder = 0;
        current_head = 0;
        disk_inserted = false;
        write_protected = false;
        motor_on = false;
        disk_changed = false;

        read_count = 0;
        write_count = 0;
        seek_count = 0;
        format_count = 0;
        error_count = 0;
    }

    // Insert disk with specific format
    bool insertDisk(DiskFormat fmt, bool wp = false) {
        if (fmt == FMT_NONE || fmt > FMT_AMIGA_HD) {
            return false;
        }

        format = fmt;
        geometry = GEOMETRIES[fmt];
        write_protected = wp;
        disk_inserted = true;
        disk_changed = true;

        // Allocate disk data
        disk_data.resize(geometry.total_size, 0xF6);  // Format fill byte

        if (debug_enabled) {
            printf("FLOPPY: Inserted %s disk (%u bytes)\n",
                   geometry.name, geometry.total_size);
        }

        return true;
    }

    // Load disk image from file
    bool loadImage(const char* filename) {
        std::ifstream file(filename, std::ios::binary | std::ios::ate);
        if (!file.is_open()) {
            if (debug_enabled) {
                printf("FLOPPY: Cannot open %s\n", filename);
            }
            return false;
        }

        size_t size = file.tellg();
        file.seekg(0, std::ios::beg);

        // Determine format from size
        DiskFormat fmt = formatFromSize(size);
        if (fmt == FMT_NONE) {
            if (debug_enabled) {
                printf("FLOPPY: Unknown disk size %zu bytes\n", size);
            }
            return false;
        }

        // Initialize disk
        if (!insertDisk(fmt, false)) {
            return false;
        }

        // Read data
        file.read(reinterpret_cast<char*>(disk_data.data()), size);
        image_filename = filename;

        if (debug_enabled) {
            printf("FLOPPY: Loaded %s (%s, %zu bytes)\n",
                   filename, geometry.name, size);
        }

        return true;
    }

    // Save disk image to file
    bool saveImage(const char* filename = nullptr) {
        if (!disk_inserted) {
            return false;
        }

        const char* save_name = filename ? filename : image_filename.c_str();
        if (!save_name || strlen(save_name) == 0) {
            return false;
        }

        std::ofstream file(save_name, std::ios::binary);
        if (!file.is_open()) {
            if (debug_enabled) {
                printf("FLOPPY: Cannot create %s\n", save_name);
            }
            return false;
        }

        file.write(reinterpret_cast<const char*>(disk_data.data()),
                   disk_data.size());

        if (debug_enabled) {
            printf("FLOPPY: Saved to %s (%u bytes)\n",
                   save_name, (uint32_t)disk_data.size());
        }

        return true;
    }

    // Eject disk
    void ejectDisk() {
        disk_data.clear();
        format = FMT_NONE;
        geometry = GEOMETRIES[0];
        image_filename.clear();
        disk_inserted = false;
        disk_changed = true;

        if (debug_enabled) {
            printf("FLOPPY: Disk ejected\n");
        }
    }

    // Seek to cylinder
    OpStatus seek(uint8_t cylinder) {
        if (!disk_inserted) {
            error_count++;
            return OP_NO_DISK;
        }

        if (cylinder >= geometry.cylinders) {
            error_count++;
            if (debug_enabled) {
                printf("FLOPPY: Seek error - cylinder %d >= %d\n",
                       cylinder, geometry.cylinders);
            }
            return OP_SEEK_ERROR;
        }

        current_cylinder = cylinder;
        seek_count++;

        if (debug_enabled) {
            printf("FLOPPY: Seek to cylinder %d\n", cylinder);
        }

        return OP_SUCCESS;
    }

    // Recalibrate (seek to cylinder 0)
    OpStatus recalibrate() {
        return seek(0);
    }

    // Select head
    void selectHead(uint8_t head) {
        if (head < geometry.heads) {
            current_head = head;
        }
    }

    // Read sector
    OpStatus readSector(uint8_t cylinder, uint8_t head, uint8_t sector,
                        uint8_t* buffer, uint16_t& bytes_read) {
        bytes_read = 0;

        if (!disk_inserted) {
            error_count++;
            return OP_NO_DISK;
        }

        // Validate address
        if (!validateCHS(cylinder, head, sector)) {
            error_count++;
            return OP_NOT_FOUND;
        }

        // Calculate LBA
        uint32_t lba = chsToLba(cylinder, head, sector);
        uint32_t offset = lba * geometry.bytes_per_sector;

        if (offset + geometry.bytes_per_sector > disk_data.size()) {
            error_count++;
            return OP_NOT_FOUND;
        }

        // Copy data
        memcpy(buffer, &disk_data[offset], geometry.bytes_per_sector);
        bytes_read = geometry.bytes_per_sector;
        read_count++;

        if (debug_enabled) {
            printf("FLOPPY: Read C=%d H=%d S=%d (LBA %d)\n",
                   cylinder, head, sector, lba);
        }

        return OP_SUCCESS;
    }

    // Write sector
    OpStatus writeSector(uint8_t cylinder, uint8_t head, uint8_t sector,
                         const uint8_t* buffer, uint16_t bytes_to_write) {
        if (!disk_inserted) {
            error_count++;
            return OP_NO_DISK;
        }

        if (write_protected) {
            error_count++;
            if (debug_enabled) {
                printf("FLOPPY: Write protected\n");
            }
            return OP_WRITE_PROTECT;
        }

        // Validate address
        if (!validateCHS(cylinder, head, sector)) {
            error_count++;
            return OP_NOT_FOUND;
        }

        // Calculate LBA
        uint32_t lba = chsToLba(cylinder, head, sector);
        uint32_t offset = lba * geometry.bytes_per_sector;

        if (offset + geometry.bytes_per_sector > disk_data.size()) {
            error_count++;
            return OP_NOT_FOUND;
        }

        // Write data
        uint16_t write_bytes = (bytes_to_write < geometry.bytes_per_sector) ?
                               bytes_to_write : geometry.bytes_per_sector;
        memcpy(&disk_data[offset], buffer, write_bytes);
        write_count++;

        if (debug_enabled) {
            printf("FLOPPY: Write C=%d H=%d S=%d (LBA %d)\n",
                   cylinder, head, sector, lba);
        }

        return OP_SUCCESS;
    }

    // Read multiple sectors
    OpStatus readSectors(uint8_t cylinder, uint8_t head, uint8_t start_sector,
                         uint8_t count, uint8_t* buffer, uint16_t& bytes_read) {
        bytes_read = 0;
        uint8_t sector = start_sector;

        for (int i = 0; i < count; i++) {
            uint16_t sector_bytes;
            OpStatus status = readSector(cylinder, head, sector,
                                         buffer + bytes_read, sector_bytes);
            if (status != OP_SUCCESS) {
                return status;
            }
            bytes_read += sector_bytes;
            sector++;

            // Handle track wrap
            if (sector > geometry.sectors_per_track) {
                return OP_END_OF_TRACK;
            }
        }

        return OP_SUCCESS;
    }

    // Format track
    OpStatus formatTrack(uint8_t cylinder, uint8_t head, uint8_t fill_byte = 0xF6) {
        if (!disk_inserted) {
            error_count++;
            return OP_NO_DISK;
        }

        if (write_protected) {
            error_count++;
            return OP_WRITE_PROTECT;
        }

        if (cylinder >= geometry.cylinders || head >= geometry.heads) {
            error_count++;
            return OP_FORMAT_ERROR;
        }

        // Format all sectors on track
        uint32_t track_start = (cylinder * geometry.heads + head) *
                               geometry.sectors_per_track *
                               geometry.bytes_per_sector;

        uint32_t track_size = geometry.sectors_per_track *
                              geometry.bytes_per_sector;

        if (track_start + track_size > disk_data.size()) {
            error_count++;
            return OP_FORMAT_ERROR;
        }

        memset(&disk_data[track_start], fill_byte, track_size);
        format_count++;

        if (debug_enabled) {
            printf("FLOPPY: Format track C=%d H=%d (fill=0x%02X)\n",
                   cylinder, head, fill_byte);
        }

        return OP_SUCCESS;
    }

    // Read ID (get sector header info)
    OpStatus readId(uint8_t head, uint8_t& out_cyl, uint8_t& out_head,
                    uint8_t& out_sector, uint8_t& out_size_code) {
        if (!disk_inserted) {
            error_count++;
            return OP_NO_DISK;
        }

        out_cyl = current_cylinder;
        out_head = head;
        out_sector = 1;  // Return first sector
        out_size_code = 2;  // 512 bytes (2^(n+7) = 512)

        return OP_SUCCESS;
    }

    // Motor control
    void setMotor(bool on) {
        motor_on = on;
        if (debug_enabled && on) {
            printf("FLOPPY: Motor %s\n", on ? "ON" : "OFF");
        }
    }

    // Disk changed flag
    bool isDiskChanged() {
        bool changed = disk_changed;
        disk_changed = false;  // Clear on read
        return changed;
    }

    // Get disk info
    bool isDiskInserted() const { return disk_inserted; }
    bool isWriteProtected() const { return write_protected; }
    bool isMotorOn() const { return motor_on; }
    DiskFormat getFormat() const { return format; }
    const DiskGeometry& getGeometry() const { return geometry; }
    uint8_t getCurrentCylinder() const { return current_cylinder; }
    uint8_t getCurrentHead() const { return current_head; }

    // Set write protection
    void setWriteProtection(bool wp) { write_protected = wp; }

    // Direct memory access (for testing)
    uint8_t* getDataPtr() { return disk_data.data(); }
    const uint8_t* getDataPtr() const { return disk_data.data(); }
    uint32_t getDataSize() const { return (uint32_t)disk_data.size(); }

    // Get statistics
    uint32_t getReadCount() const { return read_count; }
    uint32_t getWriteCount() const { return write_count; }
    uint32_t getSeekCount() const { return seek_count; }
    uint32_t getFormatCount() const { return format_count; }
    uint32_t getErrorCount() const { return error_count; }

    void printStats() const {
        printf("Floppy Statistics:\n");
        printf("  Reads:   %u\n", read_count);
        printf("  Writes:  %u\n", write_count);
        printf("  Seeks:   %u\n", seek_count);
        printf("  Formats: %u\n", format_count);
        printf("  Errors:  %u\n", error_count);
    }

    void printInfo() const {
        printf("Floppy Disk Info:\n");
        printf("  Inserted: %s\n", disk_inserted ? "Yes" : "No");
        if (disk_inserted) {
            printf("  Format: %s\n", geometry.name);
            printf("  Size: %u bytes\n", geometry.total_size);
            printf("  Geometry: %d cylinders, %d heads, %d sectors/track\n",
                   geometry.cylinders, geometry.heads, geometry.sectors_per_track);
            printf("  Bytes/sector: %d\n", geometry.bytes_per_sector);
            printf("  Write protected: %s\n", write_protected ? "Yes" : "No");
            printf("  Current position: C=%d H=%d\n",
                   current_cylinder, current_head);
            if (!image_filename.empty()) {
                printf("  Image file: %s\n", image_filename.c_str());
            }
        }
    }

private:
    DiskFormat formatFromSize(size_t size) {
        switch (size) {
            case 163840:  return FMT_160K;
            case 184320:  return FMT_180K;
            case 327680:  return FMT_320K;
            case 368640:  return FMT_360K;
            case 737280:  return FMT_720K;
            case 1228800: return FMT_1200K;
            case 1474560: return FMT_1440K;
            case 2949120: return FMT_2880K;
            case 901120:  return FMT_AMIGA_DD;
            case 1802240: return FMT_AMIGA_HD;
            default:      return FMT_NONE;
        }
    }

    bool validateCHS(uint8_t c, uint8_t h, uint8_t s) const {
        return (c < geometry.cylinders &&
                h < geometry.heads &&
                s >= 1 && s <= geometry.sectors_per_track);
    }

    uint32_t chsToLba(uint8_t c, uint8_t h, uint8_t s) const {
        return ((uint32_t)c * geometry.heads + h) *
               geometry.sectors_per_track + (s - 1);
    }

    CHSAddress lbaToChs(uint32_t lba) const {
        CHSAddress addr;
        uint32_t sectors_per_cylinder = geometry.heads * geometry.sectors_per_track;
        addr.cylinder = lba / sectors_per_cylinder;
        uint32_t remainder = lba % sectors_per_cylinder;
        addr.head = remainder / geometry.sectors_per_track;
        addr.sector = (remainder % geometry.sectors_per_track) + 1;
        return addr;
    }
};

// Define static constexpr member
constexpr FloppyModelCpp::DiskGeometry FloppyModelCpp::GEOMETRIES[];

#endif // FLOPPY_MODEL_CPP_H
