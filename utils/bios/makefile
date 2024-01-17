
# Compiler setup
CC := ia16-elf-gcc
AS := ia16-elf-gcc  # Assuming you use GCC for assembly as well
LD := ia16-elf-ld

# Output directory
OUTDIR := output

# Compilation flags
CFLAGS := -Wall -ffunction-sections -Werror -ffreestanding -O2 -std=gnu99 -mtune=i80186 -march=i80186
ASFLAGS := -Wall -Werror -ffreestanding -O2 -std=gnu99 -nostdinc -mtune=i80186 -march=i80186
LDFLAGS := -Map=$(OUTDIR)/bios.map -nostdlib -T bios.x  
ASMLFLAGS := -Wa,-adhln

# Source files
SOURCES_C := bios.c disk.c display.c keyboard.c leds.c mouse.c sd.c printk.c serial.c timer.c utils.c
SOURCES_ASM := entry.S mouse_asm.S

# Object files
OBJECTS_C := $(SOURCES_C:.c=.o)
OBJECTS_ASM := $(SOURCES_ASM:.S=.o)

# Target
BIOS_PLATFORM := mypc
TARGET := $(OUTDIR)/bios-$(BIOS_PLATFORM)

# Ensure output directory exists
$(shell mkdir -p $(OUTDIR))

# Build rules
.PHONY: all clean

all: $(TARGET)


	
$(TARGET): $(OBJECTS_C) $(OBJECTS_ASM)
	$(LD) $(LDFLAGS) -o $@ $(addprefix $(OUTDIR)/, $(notdir $(OBJECTS_C) $(OBJECTS_ASM)))


%.o: %.c
	#$(CC) $(CFLAGS) -c $< -o $(OUTDIR)/$@
	$(CC) $(CFLAGS) $(ASMLFLAGS) -c $< -o $(OUTDIR)/$@
	$(CC) $(CFLAGS) $(ASMLFLAGS) -S $< -o $(OUTDIR)/$(basename $@).s
%.o: %.S
	#$(AS) $(ASFLAGS) -c $< -o $(OUTDIR)/$@
	$(AS) $(ASFLAGS) $(ASMLFLAGS) -c $< -o $(OUTDIR)/$@
	$(AS) $(ASFLAGS) $(ASMLFLAGS) -S $< -o $(OUTDIR)/$(basename $@).s

clean:
	rm -rf $(OUTDIR)

# Additional macros (revised)
# Define the date format macros using shell date command


#BIOS_BUILD_DATE := $(shell date +%m/%d/%y -u)
#BIOS_BUILD_DAY := $(shell date +%d -u)
#BIOS_BUILD_MONTH := $(shell date +%m -u)
#BIOS_BUILD_YEAR := $(shell date +%Y -u)
#BIOS_BUILD_SECOND := $(shell date +%S -u)
#BIOS_BUILD_MINUTE := $(shell date +%M -u)
#BIOS_BUILD_HOUR := $(shell date +%H -u)


# Define the date format macros using shell date command
BIOS_BUILD_DATE := $(shell date +%m/%d/%y -u)
BIOS_BUILD_DAY := $(shell date +%d -u | awk '{printf "%d", $$1}')  # Remove leading zeros, keep single '0'
BIOS_BUILD_MONTH := $(shell date +%m -u | awk '{printf "%d", $$1}')  # Remove leading zeros, keep single '0'
BIOS_BUILD_YEAR := $(shell date +%Y -u)

# Formatting hours, minutes, seconds to remove leading zeros, keep single '0'
BIOS_BUILD_HOUR := $(shell date +%H -u | awk '{if ($$1 == "00") print "0"; else printf "%d", $$1}')
BIOS_BUILD_MINUTE := $(shell date +%M -u | awk '{if ($$1 == "00") print "0"; else printf "%d", $$1}')
BIOS_BUILD_SECOND := $(shell date +%S -u | awk '{if ($$1 == "00") print "0"; else printf "%d", $$1}')


#BIOS_BUILD_DATE := $(shell date +%m/%d/%y -u)
#BIOS_BUILD_DAY := $(shell date +%d -u)
#BIOS_BUILD_MONTH := $(shell date +%m -u | sed 's/^0*//')  # Remove leading zeros
#BIOS_BUILD_YEAR := $(shell date +%Y -u)
#BIOS_BUILD_SECOND := $(shell date +%S -u | sed 's/^0*//')  # Remove leading zeros
#BIOS_BUILD_MINUTE := $(shell date +%M -u)
#BIOS_BUILD_HOUR := $(shell date +%H -u | sed 's/^0*//')  # Remove leading zeros

# Add these macros to CFLAGS

CFLAGS += -D__PLATFORM__=\"$(BIOS_PLATFORM)\" \
          -D__BUILD__="01" \
          -DBIOS_BUILD_DATE="\"$(BIOS_BUILD_DATE)\"" \
          -DCACHE_SIZE=8192
          
          CFLAGS += -DBIOS_BUILD_HOUR=$(BIOS_BUILD_HOUR) \
          -DBIOS_BUILD_MINUTE=$(BIOS_BUILD_MINUTE) \
          -DBIOS_BUILD_SECOND=$(BIOS_BUILD_SECOND) \
          -DBIOS_BUILD_DAY=$(BIOS_BUILD_DAY) \
          -DBIOS_BUILD_MONTH=$(BIOS_BUILD_MONTH) \
          -DBIOS_BUILD_YEAR=$(BIOS_BUILD_YEAR)

# Add macro definitions to ASFLAGS
ASFLAGS += -D__PLATFORM__=\"$(BIOS_PLATFORM)\" \
           -D__BUILD__="BUILD" \
           -DBIOS_BUILD_DATE="\"$(BIOS_BUILD_DATE)\"" \
           -DBIOS_BUILD_HOUR=$(BIOS_BUILD_HOUR) \
           -DBIOS_BUILD_MINUTE=$(BIOS_BUILD_MINUTE) \
           -DBIOS_BUILD_SECOND=$(BIOS_BUILD_SECOND) \
           -DBIOS_BUILD_DAY=$(BIOS_BUILD_DAY) \
           -DBIOS_BUILD_MONTH=$(BIOS_BUILD_MONTH) \
           -DBIOS_BUILD_YEAR=$(BIOS_BUILD_YEAR) \
           -DCACHE_SIZE=8192


          
# Print the BIOS_BUILD_DATE macro
$(info BIOS_BUILD_DATE is $(BIOS_BUILD_DATE))
