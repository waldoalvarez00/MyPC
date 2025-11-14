# Quartus synthesis script for FPU_Payne_Hanek module analysis
# This script synthesizes just the Payne-Hanek module to determine area usage

# Load Quartus packages
load_package flow

# Create a new project for analysis
project_new -overwrite payne_hanek_analysis -family "Cyclone V" -part "5CSEBA6U23I7"

# Add source files
set_global_assignment -name VERILOG_FILE "rtl/FPU8087/FPU_Payne_Hanek.v"
set_global_assignment -name TOP_LEVEL_ENTITY FPU_Payne_Hanek

# Set optimization settings (same as main project)
set_global_assignment -name OPTIMIZATION_MODE "AGGRESSIVE AREA"
set_global_assignment -name OPTIMIZATION_TECHNIQUE AREA
set_global_assignment -name AUTO_RAM_RECOGNITION ON
set_global_assignment -name AUTO_ROM_RECOGNITION ON

# Run synthesis only (no fitting)
execute_module -tool map

# Report resource usage
load_report payne_hanek_analysis
set panel "Analysis & Synthesis||Analysis & Synthesis Resource Usage Summary"
if {[catch {set panel_id [get_report_panel_id $panel]} error]} {
    puts "Could not find panel: $panel"
} else {
    set row_cnt [get_number_of_rows -id $panel_id]
    for {set i 1} {$i < $row_cnt} {incr i} {
        set row [get_report_panel_row -id $panel_id -row $i]
        puts [join $row " | "]
    }
}

unload_report
project_close
