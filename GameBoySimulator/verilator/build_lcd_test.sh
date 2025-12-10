#!/bin/bash

echo "Building LCD DMG output test..."

g++ -std=c++14 \
    -I./obj_dir \
    -I/usr/local/share/verilator/include \
    -I/usr/local/share/verilator/include/vltstd \
    test_lcd_dmg_output.cpp \
    obj_dir/Vtop__ALL.a \
    /usr/local/share/verilator/include/verilated.cpp \
    -o test_lcd_dmg_output

if [ $? -eq 0 ]; then
    echo "Build successful!"
    echo "Running test..."
    timeout 60 ./test_lcd_dmg_output
else
    echo "Build failed!"
    exit 1
fi
