# MyPC

This project marks an initial attempt to port Jamie Iles' computer to the MiSTer platform. Central to its design is the incorporation of a **microassembler** for the CPU microcode, significantly enhancing the system's modifiability and maintainability. This feature is not just crucial for current adaptability but also lays a foundation for potential future enhancements, such as the integration of a **Floating Point Unit** (FPU) like an 80387 that could fit in the FPGA. The project's primary objective is to emulate the architecture and functionality of a traditional PC, emphasizing binary compatibility over cycle-accurate replication.

The system's architecture is designed around 16-bit buses, an integral element that ensures efficient data transfer for 80186 and significantly boosts overall performance. Furthermore, the system integrates **direct-mapped cache** memory, key for enhancing processing speed and data access efficiency.

A notable addition to this project is the integration of an **MCGA** (Multi-Color Graphics Array) adapter. This adapter is particularly significant for its support of Mode 13h, which allows for a display of **256 colors**. Moreover, the controller uses SDRAM for video, which is shared with the CPU. This shared memory architecture not only optimizes the current graphics capabilities but also paves the way for future developments, such as the potential implementation of a VGA adapter, further expanding the system's graphical versatility.

The integration of Mode 13h in the MCGA adapter is a crucial aspect of this project, reflecting a deep commitment to replicating not just the operational characteristics of traditional PCs but also their rich graphical output. By supporting a 256-color display, Mode 13h enables a more vibrant and visually engaging emulation experience on the MiSTer platform. This feature is key to capturing the essence of classic computing graphics, thereby enhancing the overall authenticity and appeal of the emulation.
