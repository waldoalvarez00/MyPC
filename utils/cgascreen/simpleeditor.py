# Copyright 2025, Waldo Alvarez, https://pipflow.com

ROWS = 25  # Number of rows in the text mode
COLS = 80  # Number of columns in the text mode

def parse_memory_dump(file_path):
    with open(file_path, 'r') as file:
        content = file.read()
        bytes_hex = content.split()
        return [(int(bytes_hex[i], 16), int(bytes_hex[i+1], 16)) for i in range(0, len(bytes_hex), 2)]
		


def print_attribute_guide():
    print("\nAttribute Guide:")
    print("Hex  | Description")
    print("------------------")
    print("0x00 | Black")
    print("0x01 | Blue")
    print("0x02 | Green")
    print("0x03 | Cyan")
    print("0x04 | Red")
    print("0x05 | Magenta")
    print("0x06 | Brown")
    print("0x07 | Light Gray")
    print("0x08 | Dark Gray")
    print("0x09 | Light Blue")
    print("0x0A | Light Green")
    print("0x0B | Light Cyan")
    print("0x0C | Light Red")
    print("0x0D | Light Magenta")
    print("0x0E | Yellow")
    print("0x0F | White")
    print("\nPlease enter the attribute in hexadecimal (e.g., 0E for Yellow).")


# CGA to ANSI color mapping (simplified) for foreground and background
cga_to_ansi_colors = {
    0x0: 30, # Black
    0x1: 34, # Blue
    0x2: 32, # Green
    0x3: 36, # Cyan
    0x4: 31, # Red
    0x5: 35, # Magenta
    0x6: 33, # Brown/Yellow
    0x7: 37, # Light Gray/White
    0x8: 90, # Dark Gray
    0x9: 94, # Light Blue
    0xA: 92, # Light Green
    0xB: 96, # Light Cyan
    0xC: 91, # Light Red
    0xD: 95, # Light Magenta
    0xE: 93, # Yellow
    0xF: 97  # Bright White
}

# Update the print_video_memory function to include background colors
def print_video_memory(video_memory):
    # Print top row for columns marked at intervals of 10
    top_row_marker = " " * 3  # Initial spacing for alignment with the row numbers below
    for i in range(COLS // 10):
        top_row_marker += str(i * 10).ljust(10)
    top_row_marker += str(COLS // 10 * 10)  # Add the last marker if needed
    print(top_row_marker[:COLS + 3])  # Ensure it fits the screen width exactly
    
    # Print second top row with numbers 0 to 9 repeating
    print("   " + "".join(str(i) for i in range(10)) * (COLS // 10) + "".join(str(i) for i in range(COLS % 10)))
    
    for row in range(ROWS):
        print(f"{row:2} ", end='')  # Print row number
        for col in range(COLS):
            index = row * COLS + col
            if index < len(video_memory):
                char, attr = video_memory[index]
                fg_color = attr & 0x0F
                bg_color = (attr >> 4) & 0x0F
                fg_ansi = cga_to_ansi_colors.get(fg_color, 97)
                bg_ansi = cga_to_ansi_colors.get(bg_color, 40) - 30 + 40  # Convert foreground color to background
                # Print character with ANSI color codes for foreground and background
                print(f'\033[{fg_ansi};{bg_ansi}m{chr(char)}\033[0m', end='')
            else:
                break
        print()  # Newline after each row


def edit_video_memory(video_memory):
    while True:
        print("\nEnter position to edit (row,col), or 'done' to finish:")
        input_pos = input().strip()
        if input_pos.lower() == 'done':
            break
        
        try:
            row, col = map(int, input_pos.split(','))
            assert 0 <= row < ROWS and 0 <= col < COLS
        except (ValueError, AssertionError):
            print("Invalid input. Please enter in format 'row,col' within valid range.")
            continue

        char = input("Enter new character: ").strip()
        if char == '':  # Check if the character is empty
            char = ' '  # Set character to space if empty
        
        print_attribute_guide()  # Display the attribute guide
        attr = input("Enter new attribute (hexadecimal, e.g., 1E): ").strip()

        try:
            char_code = ord(char[0])  # Take only the first character, which is now guaranteed to be not empty
            attr_code = int(attr, 16)
            assert 0 <= attr_code <= 0xFF
        except (TypeError, ValueError, AssertionError):
            print("Invalid character or attribute. Please enter valid values.")
            continue

        modify_video_memory(video_memory, (row, col), char_code, attr_code)
        print("\nUpdated Video Memory:")
        print_video_memory(video_memory)



def save_video_memory(video_memory, save_file_path):
    with open(save_file_path, 'w') as file:
        for char, attr in video_memory:
            file.write(f'{char:02X} {attr:02X} ')
        print(f"\nVideo memory saved to {save_file_path}")

def modify_video_memory(video_memory, position, char, attr):
    if 0 <= position[0] < ROWS and 0 <= position[1] < COLS:
        index = position[0] * COLS + position[1]
        if index < len(video_memory):  # Check to avoid index out of range
            video_memory[index] = (char, attr)

if __name__ == "__main__":
    file_path = 'splash.hex'
    video_memory = parse_memory_dump(file_path)

    print("Initial Video Memory Content:")
    print_video_memory(video_memory)

    # Interactive editing loop
    edit_video_memory(video_memory)

    # Save the modified video memory to a file
    save_file_path = input("\nEnter the name of the file to save the modified video memory dump: ")
    save_video_memory(video_memory, save_file_path)




