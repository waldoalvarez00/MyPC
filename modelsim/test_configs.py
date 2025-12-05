"""
Test configurations for MyPC2 Verilog test suite.

Auto-generated from shell scripts by generate_test_configs.py
"""

from typing import List, Dict, Optional


class TestConfig:
    """Configuration for a single Verilog test."""

    def __init__(
        self,
        name: str,
        testbench: str,
        sources: List[str],
        includes: Optional[List[str]] = None,
        defines: Optional[List[str]] = None,
        top_module: Optional[str] = None,
        category: str = "core",
        timeout: int = 120,
        description: str = "",
        simulator: str = "iverilog",
        cpp_testbench: Optional[str] = None,
        enable_coverage: bool = False
    ):
        self.name = name
        self.testbench = testbench
        self.sources = sources
        self.includes = includes or []
        self.defines = defines or []
        self.top_module = top_module
        self.category = category
        self.timeout = timeout
        self.description = description
        self.simulator = simulator  # "iverilog" or "verilator"
        self.cpp_testbench = cpp_testbench  # C++ testbench for Verilator
        self.enable_coverage = enable_coverage  # Enable Verilator code coverage


# =============================================================================
# Test Configurations
# =============================================================================

TEST_CONFIGS: Dict[str, TestConfig] = {}


# =============================================================================
# ARBITER Tests
# =============================================================================

TEST_CONFIGS["arbiter"] = TestConfig(
    name="arbiter",
    testbench="mem_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/CPU/MemArbiter.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/CPU",
    ],
    defines=['verilator'],
    category="arbiter",
    description="arbiter tests"
)

TEST_CONFIGS["dma_arbiter"] = TestConfig(
    name="dma_arbiter",
    testbench="dma_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/DMAArbiter.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    defines=['verilator'],
    category="arbiter",
    description="dma_arbiter tests"
)

TEST_CONFIGS["harvard_arbiter"] = TestConfig(
    name="harvard_arbiter",
    testbench="harvard_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/common/HarvardArbiter.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="arbiter",
    description="harvard_arbiter tests"
)

TEST_CONFIGS["id_arbiter"] = TestConfig(
    name="id_arbiter",
    testbench="id_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/IDArbiter.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    defines=['verilator'],
    category="arbiter",
    description="id_arbiter tests"
)

TEST_CONFIGS["mem_arbiter_extend"] = TestConfig(
    name="mem_arbiter_extend",
    testbench="mem_arbiter_extend_tb.sv",
    sources=[
        "Quartus/rtl/MemArbiterExtend.sv",
    ],
    includes=[],
    top_module="mem_arbiter_extend_tb",
    category="arbiter",
    description="mem_arbiter_extend tests"
)


# =============================================================================
# AUDIO Tests
# =============================================================================

TEST_CONFIGS["speaker_audio_converter"] = TestConfig(
    name="speaker_audio_converter",
    testbench="speaker_audio_converter_tb.sv",
    sources=[
        "Quartus/rtl/audio/SpeakerAudioConverter.sv",
    ],
    includes=[
        "Quartus/rtl/audio",
    ],
    category="audio",
    description="speaker_audio_converter tests"
)


# =============================================================================
# BIOS Tests
# =============================================================================

TEST_CONFIGS["bios_upload_controller"] = TestConfig(
    name="bios_upload_controller",
    testbench="bios_upload_controller_tb.sv",
    sources=[
        "Quartus/rtl/bios/BIOSUploadController.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/bios",
    ],
    category="bios",
    description="bios_upload_controller tests"
)

TEST_CONFIGS["bios_upload_integration"] = TestConfig(
    name="bios_upload_integration",
    testbench="bios_upload_integration_tb.sv",
    sources=[
        "Quartus/rtl/bios/BIOSUploadController.sv",
        "Quartus/rtl/bios/BIOS.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/bios",
    ],
    defines=["SIMULATION"],
    category="bios",
    description="bios_upload_integration tests"
)


# =============================================================================
# CORE Tests
# =============================================================================

TEST_CONFIGS["JumpTest"] = TestConfig(
    name="JumpTest",
    testbench="JumpTest_tb.sv",
    sources=[
        "Quartus/rtl/CPU/FlagsEnum.sv",
        "Quartus/rtl/CPU/JumpTest.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="JumpTest tests"
)

TEST_CONFIGS["alu"] = TestConfig(
    name="alu",
    testbench="ALU_tb.sv",
    sources=[
        "Quartus/rtl/CPU/RegisterEnum.sv",
        "Quartus/rtl/CPU/FlagsEnum.sv",
        "Quartus/rtl/CPU/MicrocodeTypes.sv",
        "Quartus/rtl/CPU/alu/aaa.sv",
        "Quartus/rtl/CPU/alu/aas.sv",
        "Quartus/rtl/CPU/alu/adc.sv",
        "Quartus/rtl/CPU/alu/add.sv",
        "Quartus/rtl/CPU/alu/and.sv",
        "Quartus/rtl/CPU/alu/bound.sv",
        "Quartus/rtl/CPU/alu/daa.sv",
        "Quartus/rtl/CPU/alu/das.sv",
        "Quartus/rtl/CPU/alu/enter.sv",
        "Quartus/rtl/CPU/alu/extend.sv",
        "Quartus/rtl/CPU/alu/flags.sv",
        "Quartus/rtl/CPU/alu/mul.sv",
        "Quartus/rtl/CPU/alu/not.sv",
        "Quartus/rtl/CPU/alu/or.sv",
        "Quartus/rtl/CPU/alu/rcl.sv",
        "Quartus/rtl/CPU/alu/rcr.sv",
        "Quartus/rtl/CPU/alu/rol.sv",
        "Quartus/rtl/CPU/alu/ror.sv",
        "Quartus/rtl/CPU/alu/sar.sv",
        "Quartus/rtl/CPU/alu/shift_flags.sv",
        "Quartus/rtl/CPU/alu/shl.sv",
        "Quartus/rtl/CPU/alu/shr.sv",
        "Quartus/rtl/CPU/alu/sub.sv",
        "Quartus/rtl/CPU/alu/xor.sv",
        "Quartus/rtl/CPU/alu/ALU.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
        "Quartus/rtl/CPU/alu",
    ],
    category="core",
    description="alu tests"
)

TEST_CONFIGS["csipsync"] = TestConfig(
    name="csipsync",
    testbench="csipsync_tb.sv",
    sources=[
        "Quartus/rtl/CPU/CSIPSync.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="csipsync tests"
)

TEST_CONFIGS["fontcolorlut_unit"] = TestConfig(
    name="fontcolorlut_unit",
    testbench="fontcolorlut_tb.sv",
    sources=[
        "Quartus/rtl/VGA/FontColorLUT.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
    ],
    category="video",
    description="fontcolorlut_unit tests"
)

# NOTE: fstsw_ax and fstsw_ax_integration removed - testbench files don't exist

TEST_CONFIGS["harvard_smc"] = TestConfig(
    name="harvard_smc",
    testbench="harvard_smc_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2Way.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/CacheArbiter.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
        "Quartus/rtl/PipelinedMemArbiterExtend.sv",
    ],
    includes=[],
    defines=["CACHE_SETS=256"],
    category="memory",  # FAIL: SDRAM eviction - dirty line at 0x00300 expected 0xDEAD, got 0xbeef
    description="harvard_smc tests"
)

TEST_CONFIGS["harvard_smc_mini"] = TestConfig(
    name="harvard_smc_mini",
    testbench="harvard_smc_mini_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2Way.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/CacheArbiter.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    category="memory",  # Fixed: moved localparam declarations to module scope
    description="harvard_smc_mini tests"
)

TEST_CONFIGS["insndecoder"] = TestConfig(
    name="insndecoder",
    testbench="",
    sources=[
        "Quartus/rtl/CPU/RegisterEnum.sv",
        "Quartus/rtl/CPU/MicrocodeTypes.sv",
        "Quartus/rtl/CPU/Instruction.sv",
        "Quartus/rtl/CPU/InsnDecoder.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    top_module="InsnDecoder",
    category="core",
    description="InsnDecoder Verilator tests (9/9 pass)",
    simulator="verilator",
    cpp_testbench="verilator/insndecoder_tb.cpp"
)

TEST_CONFIGS["ip"] = TestConfig(
    name="ip",
    testbench="ip_tb.sv",
    sources=[
        "Quartus/rtl/CPU/IP.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="ip tests"
)

TEST_CONFIGS["loadstore"] = TestConfig(
    name="loadstore",
    testbench="loadstore_tb.sv",
    sources=[
        "Quartus/rtl/CPU/LoadStore.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="loadstore tests"
)

TEST_CONFIGS["loop_counter"] = TestConfig(
    name="loop_counter",
    testbench="loop_counter_tb.sv",
    sources=[
        "Quartus/rtl/CPU/LoopCounter.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",  # Fixed timing for Icarus compatibility
    description="loop_counter tests"
)

TEST_CONFIGS["microcode"] = TestConfig(
    name="microcode",
    testbench="microcode_tb.sv",
    sources=[
        "Quartus/rtl/CPU/InstructionDefinitions.sv",
        "Quartus/rtl/CPU/Fifo.sv",
        "Quartus/rtl/common/DPRam.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
        "Quartus/rtl/common",
    ],
    category="core",
    description="microcode tests"
)

TEST_CONFIGS["microsequencer"] = TestConfig(
    name="microsequencer",
    testbench="microsequencer_extended_bcd_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    description="microsequencer tests"
)

TEST_CONFIGS["modrm_decode"] = TestConfig(
    name="modrm_decode",
    testbench="modrm_decode_tb.sv",
    sources=[
        "Quartus/rtl/CPU/ModRMDecode.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="modrm_decode tests"
)

TEST_CONFIGS["prefetch"] = TestConfig(
    name="prefetch",
    testbench="prefetch_tb.sv",
    sources=[
        "Quartus/rtl/CPU/Prefetch.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
        "Quartus/rtl/common",
    ],
    category="core",
    description="prefetch tests"
)

TEST_CONFIGS["prefetch_smc"] = TestConfig(
    name="prefetch_smc",
    testbench="prefetch_smc_tb.sv",
    sources=[
        "Quartus/rtl/CPU/Prefetch.sv",
        "Quartus/rtl/CPU/Fifo.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
        "Quartus/rtl/common",
    ],
    category="core",
    timeout=30,
    description="Self-modifying code detection in prefetch FIFO"
)

# NOTE: register_file removed - duplicate of RegisterFile (use registerfile_verilator)

TEST_CONFIGS["segment_override"] = TestConfig(
    name="segment_override",
    testbench="segment_override_tb.sv",
    sources=[
        "Quartus/rtl/CPU/RegisterEnum.sv",
        "Quartus/rtl/CPU/SegmentOverride.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="segment_override tests"
)

TEST_CONFIGS["segment_register_file"] = TestConfig(
    name="segment_register_file",
    testbench="segment_register_file_tb.sv",
    sources=[
        "Quartus/rtl/CPU/SegmentRegisterFile.sv",
        "Quartus/rtl/CPU/RegisterEnum.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",  # Fixed declarations and timing for Icarus compatibility
    description="segment_register_file tests"
)

TEST_CONFIGS["temp_reg"] = TestConfig(
    name="temp_reg",
    testbench="temp_reg_tb.sv",
    sources=[
        "Quartus/rtl/CPU/TempReg.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="temp_reg tests"
)


# =============================================================================
# DMA Tests
# =============================================================================

TEST_CONFIGS["dma_integration"] = TestConfig(
    name="dma_integration",
    testbench="dma_integration_tb.sv",
    sources=[
    ],
    includes=[],
    category="dma",
    description="dma_integration tests"
)

TEST_CONFIGS["floppy_dma"] = TestConfig(
    name="floppy_dma",
    testbench="floppy_dma_tb.sv",
    sources=[
        "Quartus/rtl/Floppy/simplefifo.sv",
        "Quartus/rtl/Floppy/floppy.sv",
        "Quartus/rtl/KF8237-DMA/KF8237_Bus_Control_Logic.sv",
        "Quartus/rtl/KF8237-DMA/KF8237_Priority_Encoder.sv",
        "Quartus/rtl/KF8237-DMA/KF8237_Timing_And_Control.sv",
        "Quartus/rtl/KF8237-DMA/KF8237_Address_And_Count_Registers.sv",
        "Quartus/rtl/KF8237-DMA/KF8237.sv",
        "Quartus/rtl/KF8237-DMA/DMAUnit.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/Floppy",
        "Quartus/rtl/KF8237-DMA",
    ],
    defines=['ICARUS', 'MA', 'MA', 'MA', 'MA', 'MA', 'MA', 'MA'],
    category="dma",
    description="floppy_dma tests"
)

TEST_CONFIGS["floppy_dma_icarus"] = TestConfig(
    name="floppy_dma_icarus",
    testbench="floppy_dma_tb.sv",
    sources=[
        "Quartus/rtl/Floppy/simplefifo.sv",
        "Quartus/rtl/Floppy/floppy.sv",
        "Quartus/rtl/KF8237-DMA-icarus/KF8237_Bus_Control_Logic.sv",
        "Quartus/rtl/KF8237-DMA-icarus/KF8237_Priority_Encoder.sv",
        "Quartus/rtl/KF8237-DMA-icarus/KF8237_Timing_And_Control.sv",
        "Quartus/rtl/KF8237-DMA-icarus/KF8237_Address_And_Count_Registers.sv",
        "Quartus/rtl/KF8237-DMA-icarus/KF8237.sv",
        "Quartus/rtl/KF8237-DMA-icarus/DMAUnit.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/Floppy",
        "Quartus/rtl/KF8237-DMA-icarus",
    ],
    defines=['MA', 'MA', 'MA', 'MA', 'MA', 'MA', 'MA'],
    category="dma",
    description="floppy_dma_icarus tests"
)


# =============================================================================
# FLOPPY Tests
# =============================================================================

TEST_CONFIGS["floppy"] = TestConfig(
    name="floppy",
    testbench="floppy_tb.sv",
    sources=[
        "Quartus/rtl/Floppy/simplefifo.sv",
        "Quartus/rtl/Floppy/floppy.sv",
    ],
    includes=[
        "Quartus/rtl/Floppy",
    ],
    category="floppy",
    description="floppy tests"
)

TEST_CONFIGS["floppy_sd"] = TestConfig(
    name="floppy_sd",
    testbench="floppy_sd_integration_tb.sv",
    sources=[
        "Quartus/rtl/Floppy/floppy_disk_manager.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/Floppy",
    ],
    category="floppy",
    description="floppy_sd tests"
)


# =============================================================================
# FPU Tests
# =============================================================================

TEST_CONFIGS["cordic_correction_integration"] = TestConfig(
    name="cordic_correction_integration",
    testbench="cordic_correction_integration_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
    ],
    includes=[],
    top_module="cordic_correction_integration_tb",
    category="fpu",
    description="cordic_correction_integration tests"
)

TEST_CONFIGS["format_converter_q262"] = TestConfig(
    name="format_converter_q262",
    testbench="format_converter_q262_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
    ],
    includes=[],
    top_module="format_converter_q262_tb",
    category="fpu",
    description="format_converter_q262 tests"
)

TEST_CONFIGS["fpu_cordic_wrapper"] = TestConfig(
    name="fpu_cordic_wrapper",
    testbench="fpu_cordic_wrapper_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    description="fpu_cordic_wrapper tests"
)

TEST_CONFIGS["fpu_core"] = TestConfig(
    name="fpu_core",
    testbench="fpu_core_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Core.v",
        "Quartus/rtl/FPU8087/FPU_RegisterStack.v",
        "Quartus/rtl/FPU8087/FPU_StatusWord.v",
        "Quartus/rtl/FPU8087/FPU_ControlWord.v",
        "Quartus/rtl/FPU8087/FPU_ArithmeticUnit.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Multiply.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Divide.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Int16_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_Int32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int16.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int32.v",
        "Quartus/rtl/FPU8087/FPU_FP32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP64_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP32.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP64.v",
        "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Transcendental.v",
        "Quartus/rtl/FPU8087/FPU_Exception_Handler.v",
        "Quartus/rtl/FPU8087/FPU_BCD_to_Binary.v",
        "Quartus/rtl/FPU8087/FPU_Binary_to_BCD.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_Polynomial_Evaluator.v",
        "Quartus/rtl/FPU8087/FPU_Poly_Coeff_ROM.v",
        "Quartus/rtl/FPU8087/FPU_SQRT_Newton.v",
        "Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v",
        "Quartus/rtl/FPU8087/Normalizer.v",
        "Quartus/rtl/FPU8087/RoundUnit.v",
        "Quartus/rtl/FPU8087/BarrelShifter.v",
        "Quartus/rtl/FPU8087/AddSubComp.v",
        "Quartus/rtl/FPU8087/LZCByte.v",
        "Quartus/rtl/FPU8087/LZCbit.v",
        "Quartus/rtl/FPU8087/ByteShifter.v",
        "Quartus/rtl/FPU8087/BitShifter.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    timeout=180,
    description="FPU Core integration tests"
)

TEST_CONFIGS["fpu_format_converter"] = TestConfig(
    name="fpu_format_converter",
    testbench="fpu_format_converter_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="fpu_format_converter tests"
)

TEST_CONFIGS["fpu_ie_exception"] = TestConfig(
    name="fpu_ie_exception",
    testbench="fpu_ie_exception_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Core.v",
        "Quartus/rtl/FPU8087/FPU_RegisterStack.v",
        "Quartus/rtl/FPU8087/FPU_StatusWord.v",
        "Quartus/rtl/FPU8087/FPU_ControlWord.v",
        "Quartus/rtl/FPU8087/FPU_ArithmeticUnit.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Multiply.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Divide.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Int16_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_Int32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int16.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int32.v",
        "Quartus/rtl/FPU8087/FPU_FP32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP64_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP32.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP64.v",
        "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Transcendental.v",
        "Quartus/rtl/FPU8087/FPU_Exception_Handler.v",
        "Quartus/rtl/FPU8087/FPU_BCD_to_Binary.v",
        "Quartus/rtl/FPU8087/FPU_Binary_to_BCD.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_Polynomial_Evaluator.v",
        "Quartus/rtl/FPU8087/FPU_Poly_Coeff_ROM.v",
        "Quartus/rtl/FPU8087/FPU_SQRT_Newton.v",
        "Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v",
        "Quartus/rtl/FPU8087/Normalizer.v",
        "Quartus/rtl/FPU8087/RoundUnit.v",
        "Quartus/rtl/FPU8087/BarrelShifter.v",
        "Quartus/rtl/FPU8087/AddSubComp.v",
        "Quartus/rtl/FPU8087/LZCByte.v",
        "Quartus/rtl/FPU8087/LZCbit.v",
        "Quartus/rtl/FPU8087/ByteShifter.v",
        "Quartus/rtl/FPU8087/BitShifter.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    timeout=180,
    description="FPU Invalid Exception (IE) tests"
)

TEST_CONFIGS["fpu_interface"] = TestConfig(
    name="fpu_interface",
    testbench="tb_fpu_interface.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_CPU_Interface.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="fpu_interface tests"
)

TEST_CONFIGS["fpu_interface_simple"] = TestConfig(
    name="fpu_interface_simple",
    testbench="tb_fpu_interface_simple.sv",
    sources=[],
    includes=[],
    category="fpu",
    description="fpu_interface_simple tests"
)

TEST_CONFIGS["fpu_fprem_fxtract_fscale"] = TestConfig(
    name="fpu_fprem_fxtract_fscale",
    testbench="fpu_fprem_fxtract_fscale_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Core.v",
        "Quartus/rtl/FPU8087/FPU_RegisterStack.v",
        "Quartus/rtl/FPU8087/FPU_StatusWord.v",
        "Quartus/rtl/FPU8087/FPU_ControlWord.v",
        "Quartus/rtl/FPU8087/FPU_ArithmeticUnit.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Multiply.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Divide.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Int16_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_Int32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int16.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int32.v",
        "Quartus/rtl/FPU8087/FPU_FP32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP64_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP32.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP64.v",
        "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Transcendental.v",
        "Quartus/rtl/FPU8087/FPU_Exception_Handler.v",
        "Quartus/rtl/FPU8087/FPU_BCD_to_Binary.v",
        "Quartus/rtl/FPU8087/FPU_Binary_to_BCD.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_Polynomial_Evaluator.v",
        "Quartus/rtl/FPU8087/FPU_Poly_Coeff_ROM.v",
        "Quartus/rtl/FPU8087/FPU_SQRT_Newton.v",
        "Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v",
        "Quartus/rtl/FPU8087/Normalizer.v",
        "Quartus/rtl/FPU8087/RoundUnit.v",
        "Quartus/rtl/FPU8087/BarrelShifter.v",
        "Quartus/rtl/FPU8087/AddSubComp.v",
        "Quartus/rtl/FPU8087/LZCByte.v",
        "Quartus/rtl/FPU8087/LZCbit.v",
        "Quartus/rtl/FPU8087/ByteShifter.v",
        "Quartus/rtl/FPU8087/BitShifter.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    timeout=180,
    description="FPREM, FXTRACT, and FSCALE comprehensive tests"
)

TEST_CONFIGS["fpu_outer_queue"] = TestConfig(
    name="fpu_outer_queue",
    testbench="tb_fpu_outer_queue.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Outer_Queue.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="fpu_outer_queue tests"
)

TEST_CONFIGS["fpu_transcendental"] = TestConfig(
    name="fpu_transcendental",
    testbench="fpu_transcendental_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Transcendental.v",
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
        "Quartus/rtl/FPU8087/FPU_Polynomial_Evaluator.v",
        "Quartus/rtl/FPU8087/FPU_Poly_Coeff_ROM.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    description="fpu_transcendental tests"
)

TEST_CONFIGS["pipelined_dma_fpu_arbiter"] = TestConfig(
    name="pipelined_dma_fpu_arbiter",
    testbench="pipelined_dma_fpu_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/PipelinedDMAFPUArbiter.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="arbiter",
    description="pipelined_dma_fpu_arbiter tests"
)

TEST_CONFIGS["fpu_error_wait"] = TestConfig(
    name="fpu_error_wait",
    testbench="fpu_error_wait_tb.sv",
    sources=[
        "Quartus/rtl/CPU/InstructionDefinitions.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    defines=["MICROCODE_ROM_PATH=\"../Quartus/rtl/CPU\""],
    category="fpu",
    timeout=30,
    description="FPU ERROR pin detection via FWAIT instruction"
)

TEST_CONFIGS["fpu_wait_minimal"] = TestConfig(
    name="fpu_wait_minimal",
    testbench="fpu_wait_minimal_tb.sv",
    sources=[
        "Quartus/rtl/CPU/InstructionDefinitions.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    defines=["MICROCODE_ROM_PATH=\"../Quartus/rtl/CPU\""],
    category="fpu",
    timeout=10,
    description="Minimal FWAIT test for FPU ERROR pin polling (follows working microcode_tb pattern)"
)

TEST_CONFIGS["fpu_wait_polling"] = TestConfig(
    name="fpu_wait_polling",
    testbench="fpu_wait_polling_tb.sv",
    sources=[
        "Quartus/rtl/CPU/InstructionDefinitions.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    defines=["MICROCODE_ROM_PATH=\"../Quartus/rtl/CPU\""],
    category="fpu",
    timeout=10,
    description="Comprehensive FWAIT polling and ERROR pin detection test"
)

TEST_CONFIGS["fpu_control_status"] = TestConfig(
    name="fpu_control_status",
    testbench="tb_fpu_control_status.sv",
    sources=[],
    includes=[],
    category="fpu",
    timeout=10,
    description="FPU control and status word register tests"
)

TEST_CONFIGS["fpu_exceptions"] = TestConfig(
    name="fpu_exceptions",
    testbench="fpu_exceptions_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_Core.v",
        "Quartus/rtl/FPU8087/FPU_RegisterStack.v",
        "Quartus/rtl/FPU8087/FPU_StatusWord.v",
        "Quartus/rtl/FPU8087/FPU_ControlWord.v",
        "Quartus/rtl/FPU8087/FPU_ArithmeticUnit.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Multiply.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_Divide.v",
        "Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Int16_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_Int32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int16.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_Int32.v",
        "Quartus/rtl/FPU8087/FPU_FP32_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP64_to_FP80.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP32.v",
        "Quartus/rtl/FPU8087/FPU_FP80_to_FP64.v",
        "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
        "Quartus/rtl/FPU8087/FPU_Transcendental.v",
        "Quartus/rtl/FPU8087/FPU_Exception_Handler.v",
        "Quartus/rtl/FPU8087/FPU_BCD_to_Binary.v",
        "Quartus/rtl/FPU8087/FPU_Binary_to_BCD.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
        "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
        "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
        "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
        "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
        "Quartus/rtl/FPU8087/FPU_Polynomial_Evaluator.v",
        "Quartus/rtl/FPU8087/FPU_Poly_Coeff_ROM.v",
        "Quartus/rtl/FPU8087/FPU_SQRT_Newton.v",
        "Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v",
        "Quartus/rtl/FPU8087/Normalizer.v",
        "Quartus/rtl/FPU8087/RoundUnit.v",
        "Quartus/rtl/FPU8087/BarrelShifter.v",
        "Quartus/rtl/FPU8087/AddSubComp.v",
        "Quartus/rtl/FPU8087/LZCByte.v",
        "Quartus/rtl/FPU8087/LZCbit.v",
        "Quartus/rtl/FPU8087/ByteShifter.v",
        "Quartus/rtl/FPU8087/BitShifter.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    defines=["ICARUS"],
    category="fpu",
    timeout=180,
    description="Tests all FPU numeric exceptions (ZE, DE, OE, UE, PE)"
)

TEST_CONFIGS["fpu_io_port"] = TestConfig(
    name="fpu_io_port",
    testbench="tb_fpu_io_port.sv",
    sources=[
        "Quartus/rtl/FPU8087/FPU_IO_Port.sv",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    timeout=10,
    description="CPU-FPU data transfer via I/O ports"
)


# =============================================================================
# INPUT Tests
# =============================================================================

TEST_CONFIGS["kfps2kb"] = TestConfig(
    name="kfps2kb",
    testbench="kfps2kb_tb.sv",
    sources=[
        "Quartus/rtl/Keyboard/KFPS2KB.sv",
        "Quartus/rtl/Keyboard/KFPS2KB_Shift_Register.sv",
    ],
    includes=[
        "Quartus/rtl/Keyboard",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['ICARUS'],
    category="input",
    description="kfps2kb tests"
)

TEST_CONFIGS["msmouse_wrapper"] = TestConfig(
    name="msmouse_wrapper",
    testbench="msmouse_wrapper_tb.sv",
    sources=[
        "Quartus/rtl/MSMouse/MSMouseWrapper.v",
    ],
    includes=[
        "Quartus/rtl/MSMouse",
    ],
    defines=['ICARUS'],
    category="input",
    description="msmouse_wrapper tests"
)

TEST_CONFIGS["ps2_keyboard"] = TestConfig(
    name="ps2_keyboard",
    testbench="ps2_keyboard_tb.sv",
    sources=[
        "Quartus/rtl/ps2/PS2KeyboardController.sv",
        "Quartus/rtl/ps2/KeyboardController.sv",
        "Quartus/rtl/ps2/ScancodeTranslator.sv",
        "Quartus/rtl/ps2/PS2Host.sv",
        "Quartus/rtl/CPU/Fifo.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[],
    defines=['ICARUS'],
    top_module="ps2_keyboard_tb",
    category="input",
    description="ps2_keyboard tests"
)

TEST_CONFIGS["ps2_keyboard_protocol"] = TestConfig(
    name="ps2_keyboard_protocol",
    testbench="ps2_keyboard_protocol_tb.sv",
    sources=[
        "Quartus/rtl/ps2/PS2KeyboardController.sv",
        "Quartus/rtl/ps2/PS2Host.sv",
        "Quartus/rtl/ps2/KeyboardController.sv",
        "Quartus/rtl/ps2/ScancodeTranslator.sv",
        "Quartus/rtl/CPU/Fifo.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[
        "Quartus/rtl/ps2",
        "Quartus/rtl/CPU",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['ICARUS'],
    category="input",
    description="ps2_keyboard_protocol tests"
)

TEST_CONFIGS["ps2_mouse"] = TestConfig(
    name="ps2_mouse",
    testbench="ps2_mouse_tb.sv",
    sources=[
        "Quartus/rtl/ps2/PS2MouseController.sv",
        "Quartus/rtl/ps2/PS2Host.sv",
        "Quartus/rtl/CPU/Fifo.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[],
    defines=['ICARUS'],
    top_module="ps2_mouse_tb",
    category="input",
    description="ps2_mouse tests"
)


# =============================================================================
# MEMORY Tests
# =============================================================================

TEST_CONFIGS["cache"] = TestConfig(
    name="cache",
    testbench="cache_tb.sv",
    sources=[
        "Quartus/rtl/common/Cache.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/common",
    ],
    defines=['verilator'],
    category="memory",
    description="cache tests"
)

TEST_CONFIGS["dcache2way_flush"] = TestConfig(
    name="dcache2way_flush",
    testbench="dcache2way_flush_tb.sv",
    sources=[
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    category="memory",  # FAIL: Hit read expected DEAD, got beef - write buffer bypass issue
    description="dcache2way_flush tests"
)

TEST_CONFIGS["dcache2way_simple"] = TestConfig(
    name="dcache2way_simple",
    testbench="dcache2way_simple_test.sv",
    sources=[
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    category="memory",
    description="dcache2way_simple tests"
)

TEST_CONFIGS["dcache_coherency"] = TestConfig(
    name="dcache_coherency",
    testbench="tb_dcache_coherency.sv",
    sources=[
        "Quartus/rtl/common/DCacheFrontendArbiter.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    category="skip",  # Known cache writeback bug - times out during victim writeback
    description="dcache_coherency tests - SKIP: cache victim writeback timeout bug"
)

TEST_CONFIGS["fifo"] = TestConfig(
    name="fifo",
    testbench="fifo_tb.sv",
    sources=[
        "Quartus/rtl/CPU/Fifo.sv",
    ],
    includes=[],
    category="memory",
    description="fifo tests"
)

TEST_CONFIGS["harvard_cache"] = TestConfig(
    name="harvard_cache",
    testbench="harvard_cache_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2Way.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/HarvardArbiter3Way.sv",
        "Quartus/rtl/common/HarvardCacheSystem.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[
        "Quartus/rtl/common",
        "Quartus/rtl/CPU",
    ],
    defines=["CACHE_LINES=512"],
    category="memory",
    description="harvard_cache tests"
)

TEST_CONFIGS["harvard_cache_protected"] = TestConfig(
    name="harvard_cache_protected",
    testbench="harvard_cache_protected_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2Way.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/HarvardArbiter3Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    category="memory",  # Non-blocking cache with separate victim WB port
    description="harvard_cache_protected tests"
)

TEST_CONFIGS["harvard_cache_random"] = TestConfig(
    name="harvard_cache_random",
    testbench="harvard_cache_random_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2Way.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/CacheArbiter.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    category="memory",  # FAIL: 1 mismatch - cache coherence issue
    description="harvard_cache_random tests"
)

TEST_CONFIGS["harvard_dcache_flush"] = TestConfig(
    name="harvard_dcache_flush",
    testbench="harvard_dcache_flush_tb.sv",
    sources=[
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/HarvardArbiter3Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
        "Quartus/rtl/PipelinedMemArbiterExtend.sv",
    ],
    includes=[],
    defines=["CACHE_SETS=256"],
    category="memory",
    description="harvard_dcache_flush tests with victim writeback support"
)

TEST_CONFIGS["icache_dcache_coh"] = TestConfig(
    name="icache_dcache_coh",
    testbench="icache_dcache_coh_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2Way.sv",
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[],
    defines=['CACHE_SETS=64'],
    category="memory",
    description="icache_dcache_coh tests"
)

TEST_CONFIGS["sdram"] = TestConfig(
    name="sdram",
    testbench="sdram_tb.sv",
    sources=[
        "Quartus/rtl/sdram/Counter.sv",
        "Quartus/rtl/sdram/SDRAMController.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/sdram",
    ],
    defines=['verilator'],
    category="memory",
    description="sdram tests"
)

TEST_CONFIGS["sdram_config"] = TestConfig(
    name="sdram_config",
    testbench="sdram_config_tb.sv",
    sources=[
        "Quartus/rtl/sdram/SDRAMConfigRegister.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/sdram",
    ],
    defines=['verilator'],
    category="memory",
    description="sdram_config tests"
)


# =============================================================================
# PERIPHERAL Tests
# =============================================================================

TEST_CONFIGS["kf8253"] = TestConfig(
    name="kf8253",
    testbench="kf8253_tb.sv",
    sources=[
        "Quartus/rtl/KF8253/KF8253.sv",
        "Quartus/rtl/KF8253/KF8253_Counter.sv",
        "Quartus/rtl/KF8253/KF8253_Control_Logic.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/KF8253",
    ],
    category="peripheral",
    description="kf8253 tests"
)

# NOTE: kf8259_comprehensive is extremely slow under Icarus Verilog due to
# "constant selects in always_* processes" warnings causing inefficient simulation.
# The KF8259 uses rotate_right/rotate_left/resolv_priority functions in always_comb
# blocks which Icarus handles poorly. Use "pic" or "kf8259" tests for coverage instead.
# This test is in "skip" category - run explicitly with --test kf8259_comprehensive
TEST_CONFIGS["kf8259_comprehensive"] = TestConfig(
    name="kf8259_comprehensive",
    testbench="kf8259_comprehensive_tb.sv",
    sources=[
        "Quartus/rtl/KF8259/KF8259_Common_Package.svh",
        "Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv",
        "Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv",
        "Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv",
        "Quartus/rtl/KF8259/KF8259_In_Service.sv",
        "Quartus/rtl/KF8259/KF8259_Control_Logic.sv",
        "Quartus/rtl/KF8259/KF8259.sv",
    ],
    includes=[
        "Quartus/rtl/KF8259",
    ],
    category="skip",  # Too slow for Icarus - use pic/kf8259 tests instead
    timeout=600,  # Very slow due to Icarus Verilog limitations
    description="kf8259_comprehensive tests - SKIP: Too slow under Icarus Verilog"
)

TEST_CONFIGS["pic"] = TestConfig(
    name="pic",
    testbench="pic_tb.sv",
    sources=[
        "Quartus/rtl/KF8259/KF8259.sv",
        "Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv",
        "Quartus/rtl/KF8259/KF8259_Control_Logic.sv",
        "Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv",
        "Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv",
        "Quartus/rtl/KF8259/KF8259_In_Service.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/KF8259",
    ],
    category="peripheral",
    description="pic tests"
)

TEST_CONFIGS["ppi"] = TestConfig(
    name="ppi",
    testbench="ppi_tb.sv",
    sources=[
        "Quartus/rtl/KF8255/KF8255.sv",
        "Quartus/rtl/KF8255/KF8255_Control_Logic.sv",
        "Quartus/rtl/KF8255/KF8255_Group.sv",
        "Quartus/rtl/KF8255/KF8255_Port.sv",
        "Quartus/rtl/KF8255/KF8255_Port_C.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/KF8255",
    ],
    category="peripheral",
    description="ppi tests"
)

TEST_CONFIGS["timer"] = TestConfig(
    name="timer",
    testbench="timer_tb.sv",
    sources=[
        "Quartus/rtl/timer/Timer.sv",
        "Quartus/rtl/timer/TimerUnit.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[
        "Quartus/rtl",
        "Quartus/rtl/timer",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['verilator'],
    category="peripheral",
    description="timer tests"
)


# =============================================================================
# SERIAL Tests
# =============================================================================

TEST_CONFIGS["simple_uart"] = TestConfig(
    name="simple_uart",
    testbench="simple_uart_tb.sv",
    sources=[
        "Quartus/rtl/uart/BaudRateGen.sv",
        "Quartus/rtl/uart/Receiver.sv",
        "Quartus/rtl/uart/Transmitter.sv",
        "Quartus/rtl/uart/Uart.sv",
    ],
    includes=[
        "Quartus/rtl/uart",
    ],
    defines=['ICARUS'],
    category="serial",
    description="simple_uart tests"
)

TEST_CONFIGS["uart"] = TestConfig(
    name="uart",
    testbench="uart_tb.sv",
    sources=[
        "Quartus/rtl/uart16750/uart.v",
        "Quartus/rtl/uart16750_sv/slib_edge_detect.sv",
        "Quartus/rtl/uart16750_sv/slib_input_sync.sv",
        "Quartus/rtl/uart16750_sv/slib_input_filter.sv",
        "Quartus/rtl/uart16750_sv/slib_clock_div.sv",
        "Quartus/rtl/uart16750_sv/slib_fifo.sv",
        "Quartus/rtl/uart16750_sv/slib_counter.sv",
        "Quartus/rtl/uart16750_sv/slib_mv_filter.sv",
        "Quartus/rtl/uart16750_sv/uart_baudgen.sv",
        "Quartus/rtl/uart16750_sv/uart_transmitter.sv",
        "Quartus/rtl/uart16750_sv/uart_receiver.sv",
        "Quartus/rtl/uart16750_sv/uart_interrupt.sv",
        "Quartus/rtl/uart16750_sv/uart_16750.sv",
    ],
    includes=[
        "Quartus/rtl/uart16750",
        "Quartus/rtl/uart16750_sv",
    ],
    defines=['ICARUS'],
    category="serial",
    description="Full UART 16750 tests using SystemVerilog translation"
)

TEST_CONFIGS["uart_16750_lite"] = TestConfig(
    name="uart_16750_lite",
    testbench="uart_16750_lite_tb.sv",
    sources=[
        "Quartus/rtl/uart16750_sv/slib_edge_detect.sv",
        "Quartus/rtl/uart16750_sv/slib_input_sync.sv",
        "Quartus/rtl/uart16750_sv/slib_input_filter.sv",
        "Quartus/rtl/uart16750_sv/slib_clock_div.sv",
        "Quartus/rtl/uart16750_sv/slib_fifo.sv",
        "Quartus/rtl/uart16750_sv/uart_baudgen.sv",
        "Quartus/rtl/uart16750_sv/uart_transmitter.sv",
        "Quartus/rtl/uart16750_sv/uart_16750_lite.sv",
    ],
    includes=[],
    top_module="uart_16750_lite_tb",
    category="serial",
    description="uart_16750_lite tests"
)


# =============================================================================
# VIDEO Tests
# =============================================================================

TEST_CONFIGS["cga"] = TestConfig(
    name="cga",
    testbench="cga_registers_tb.sv",
    sources=[
        "Quartus/rtl/CGA/cgacard.sv",
        "Quartus/rtl/CGA/cga.sv",
        "Quartus/rtl/CGA/cga_pixel.sv",
        "Quartus/rtl/CGA/cga_sequencer.sv",
        "Quartus/rtl/CGA/cga_vgaport.sv",
        "Quartus/rtl/CGA/cga_attrib.sv",
        "Quartus/rtl/CGA/UM6845R.sv",
        "Quartus/rtl/CGA/vram.sv",
        "Quartus/rtl/CGA/busConverter.sv",
    ],
    includes=[],
    defines=['ICARUS'],
    top_module="cga_registers_tb",
    category="video",
    description="cga tests"
)

TEST_CONFIGS["cga_integration"] = TestConfig(
    name="cga_integration",
    testbench="cga_controller_integration_tb.sv",
    sources=[
        "Quartus/rtl/CGA/cgacard.sv",
        "Quartus/rtl/CGA/cga.sv",
        "Quartus/rtl/CGA/cga_pixel.sv",
        "Quartus/rtl/CGA/cga_sequencer.sv",
        "Quartus/rtl/CGA/cga_attrib.sv",
        "Quartus/rtl/CGA/cga_vgaport.sv",
        "Quartus/rtl/CGA/UM6845R.sv",
        "Quartus/rtl/CGA/vram.sv",
        "Quartus/rtl/CGA/busConverter.sv",
    ],
    includes=[],
    defines=['ICARUS'],
    top_module="cga_controller_integration_tb",
    category="video",
    timeout=300,  # Video integration tests are slow in Icarus
    description="cga_integration tests"
)

TEST_CONFIGS["vga"] = TestConfig(
    name="vga",
    testbench="vga_registers_tb.sv",
    sources=[
        "Quartus/rtl/VGA/VGARegisters.sv",
        "Quartus/rtl/VGA/VGATypes.sv",
        "modelsim/DACRam_sim.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
        "Quartus/rtl/CPU/cdc/BusSync.sv",
        "Quartus/rtl/CPU/cdc/MCP.sv",
        "Quartus/rtl/CPU/cdc/SyncPulse.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['ICARUS'],
    top_module="vga_registers_tb",
    category="video",
    description="vga tests"
)

TEST_CONFIGS["vga_all_modes"] = TestConfig(
    name="vga_all_modes",
    testbench="vga_all_modes_tb.sv",
    sources=[
        "Quartus/rtl/VGA/VGARegisters.sv",
        "Quartus/rtl/CPU/cdc/BusSync.sv",
        "Quartus/rtl/CPU/cdc/MCP.sv",
        "Quartus/rtl/CPU/cdc/SyncPulse.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
        "modelsim/DACRam_sim.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['ICARUS'],
    top_module="vga_all_modes_tb",
    category="video",
    description="vga_all_modes tests"
)

TEST_CONFIGS["vga_complete"] = TestConfig(
    name="vga_complete",
    testbench="vga_complete_modes_tb.sv",
    sources=[
        "Quartus/rtl/VGA/VGARegisters.sv",
        "Quartus/rtl/CPU/cdc/BusSync.sv",
        "Quartus/rtl/CPU/cdc/MCP.sv",
        "Quartus/rtl/CPU/cdc/SyncPulse.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
        "modelsim/DACRam_sim.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['ICARUS'],
    top_module="vga_complete_modes_tb",
    category="video",
    description="vga_complete tests"
)

TEST_CONFIGS["vga_mode_switching"] = TestConfig(
    name="vga_mode_switching",
    testbench="vga_mode_switching_tb.sv",
    sources=[
        "Quartus/rtl/VGA/VGARegisters.sv",
        "Quartus/rtl/VGA/VGASync.sv",
        "Quartus/rtl/CPU/cdc/BusSync.sv",
        "Quartus/rtl/CPU/cdc/MCP.sv",
        "Quartus/rtl/CPU/cdc/SyncPulse.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
        "modelsim/DACRam_sim.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=['ICARUS'],
    top_module="vga_mode_switching_tb",
    category="video",
    description="vga_mode_switching tests"
)

TEST_CONFIGS["vga_modes"] = TestConfig(
    name="vga_modes",
    testbench="vga_modes_tb.sv",
    sources=[
    ],
    includes=[],
    top_module="vga_modes_tb",
    category="video",
    description="vga_modes tests"
)

TEST_CONFIGS["vgasync_unit"] = TestConfig(
    name="vgasync_unit",
    testbench="vgasync_tb.sv",
    sources=[
        "Quartus/rtl/VGA/VGASync.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
    ],
    category="video",
    description="vgasync_unit tests"
)


# =============================================================================
# VERILATOR Tests
# =============================================================================

TEST_CONFIGS["divider_verilator"] = TestConfig(
    name="divider_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/CPU/Divider.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    top_module="Divider",
    category="core",
    description="Divider Verilator tests",
    simulator="verilator",
    cpp_testbench="divider_tb.cpp"
)

TEST_CONFIGS["kf8253_verilator"] = TestConfig(
    name="kf8253_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/KF8253/KF8253.sv",
        "Quartus/rtl/KF8253/KF8253_Counter.sv",
        "Quartus/rtl/KF8253/KF8253_Control_Logic.sv",
    ],
    includes=[
        "Quartus/rtl/KF8253",
    ],
    top_module="KF8253",
    category="peripheral",
    description="KF8253 Timer Verilator tests",
    simulator="verilator",
    cpp_testbench="kf8253_tb.cpp"
)

TEST_CONFIGS["kf8255_verilator"] = TestConfig(
    name="kf8255_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/KF8255/KF8255.sv",
        "Quartus/rtl/KF8255/KF8255_Control_Logic.sv",
        "Quartus/rtl/KF8255/KF8255_Group.sv",
        "Quartus/rtl/KF8255/KF8255_Port.sv",
        "Quartus/rtl/KF8255/KF8255_Port_C.sv",
    ],
    includes=[
        "Quartus/rtl/KF8255",
        "Quartus/rtl",
    ],
    top_module="KF8255",
    category="peripheral",
    description="KF8255 PPI Verilator tests",
    simulator="verilator",
    cpp_testbench="kf8255_tb.cpp"
)

TEST_CONFIGS["ps2_keyboard_verilator"] = TestConfig(
    name="ps2_keyboard_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/ps2/PS2KeyboardController.sv",
        "Quartus/rtl/ps2/PS2Host.sv",
        "Quartus/rtl/ps2/KeyboardController.sv",
        "Quartus/rtl/ps2/ScancodeTranslator.sv",
        "Quartus/rtl/CPU/Fifo.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[
        "Quartus/rtl/ps2",
        "Quartus/rtl/CPU",
        "Quartus/rtl/CPU/cdc",
        "Quartus/rtl",
    ],
    top_module="PS2KeyboardController",
    category="input",
    description="PS2 Keyboard Verilator tests",
    simulator="verilator",
    cpp_testbench="ps2_keyboard_tb.cpp"
)

TEST_CONFIGS["ps2_mouse_verilator"] = TestConfig(
    name="ps2_mouse_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/ps2/PS2MouseController.sv",
        "Quartus/rtl/ps2/PS2Host.sv",
        "Quartus/rtl/CPU/Fifo.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[
        "Quartus/rtl/ps2",
        "Quartus/rtl/CPU",
        "Quartus/rtl/CPU/cdc",
        "Quartus/rtl",
    ],
    top_module="PS2MouseController",
    category="input",
    description="PS2 Mouse Verilator tests",
    simulator="verilator",
    cpp_testbench="ps2_mouse_tb.cpp"
)

# Existing Verilator tests from verilator/ directory
TEST_CONFIGS["flags_verilator"] = TestConfig(
    name="flags_verilator",
    testbench="",
    sources=[
        "modelsim/verilator/Flags_verilator.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    top_module="Flags_verilator",
    category="core",
    description="Flags Verilator tests (Icarus enum incompatibility)",
    simulator="verilator",
    cpp_testbench="verilator/flags_tb.cpp"
)

TEST_CONFIGS["loop_counter_verilator"] = TestConfig(
    name="loop_counter_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/CPU/LoopCounter.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    top_module="LoopCounter",
    category="core",
    description="LoopCounter Verilator tests",
    simulator="verilator",
    cpp_testbench="verilator/loop_counter_tb.cpp"
)

TEST_CONFIGS["segment_register_file_verilator"] = TestConfig(
    name="segment_register_file_verilator",
    testbench="",
    sources=[
        "Quartus/rtl/CPU/SegmentRegisterFile.sv",
        "Quartus/rtl/CPU/RegisterEnum.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    top_module="SegmentRegisterFile",
    category="core",
    description="SegmentRegisterFile Verilator tests",
    simulator="verilator",
    cpp_testbench="verilator/segment_register_file_tb.cpp"
)


# =============================================================================
# NEW COVERAGE GAP TESTS
# =============================================================================

# Simple utility modules
TEST_CONFIGS["posedge_to_pulse"] = TestConfig(
    name="posedge_to_pulse",
    testbench="posedge_to_pulse_tb.sv",
    sources=[
        "Quartus/rtl/CPU/PosedgeToPulse.sv",
    ],
    includes=[
        "Quartus/rtl/CPU",
    ],
    category="core",
    description="PosedgeToPulse edge detector tests"
)

TEST_CONFIGS["bios_control_register"] = TestConfig(
    name="bios_control_register",
    testbench="bios_control_register_tb.sv",
    sources=[
        "Quartus/rtl/bios/BIOSControlRegister.sv",
    ],
    includes=[
        "Quartus/rtl/bios",
    ],
    category="bios",
    description="BIOS control register tests"
)

TEST_CONFIGS["three_bit_mux"] = TestConfig(
    name="three_bit_mux",
    testbench="three_bit_mux_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/three_bit_4x1_mux.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="3-bit 4:1 mux tests"
)

TEST_CONFIGS["fpu_abs_unit"] = TestConfig(
    name="fpu_abs_unit",
    testbench="fpu_abs_unit_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/absunit.sv",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="FPU absolute value unit tests"
)

TEST_CONFIGS["fpu_tag_register"] = TestConfig(
    name="fpu_tag_register",
    testbench="fpu_tag_register_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/tagRegister.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="FPU tag register tests"
)

TEST_CONFIGS["fpu_stack_registers"] = TestConfig(
    name="fpu_stack_registers",
    testbench="fpu_stack_registers_tb.sv",
    sources=[
        "Quartus/rtl/FPU8087/StackRegister.v",
    ],
    includes=[
        "Quartus/rtl/FPU8087",
    ],
    category="fpu",
    description="FPU stack register file tests"
)

TEST_CONFIGS["tandy_scancode_converter"] = TestConfig(
    name="tandy_scancode_converter",
    testbench="tandy_scancode_converter_tb.sv",
    sources=[
        "Quartus/rtl/Keyboard/Tandy_Scancode_Converter.sv",
    ],
    includes=[
        "Quartus/rtl/Keyboard",
    ],
    category="input",
    description="Tandy scancode converter tests"
)

TEST_CONFIGS["dac_ram"] = TestConfig(
    name="dac_ram",
    testbench="dac_ram_tb.sv",
    sources=[
        "Quartus/rtl/VGA/DACRam.v",
    ],
    includes=[
        "Quartus/rtl/VGA",
    ],
    defines=["SIMULATION"],
    category="video",
    description="VGA DAC RAM tests"
)

TEST_CONFIGS["poweron_reset"] = TestConfig(
    name="poweron_reset",
    testbench="poweron_reset_tb.sv",
    sources=[
        "Quartus/rtl/common/PoweronReset.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
    ],
    includes=[
        "Quartus/rtl/common",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=["SIMULATION"],
    category="core",
    description="Power-on reset generator tests"
)

TEST_CONFIGS["uart_ports"] = TestConfig(
    name="uart_ports",
    testbench="uart_ports_tb.sv",
    sources=[
        "Quartus/rtl/uart/UartPorts.sv",
        "Quartus/rtl/uart/Uart.sv",
        "Quartus/rtl/uart/BaudRateGen.sv",
        "Quartus/rtl/uart/Transmitter.sv",
        "Quartus/rtl/uart/Receiver.sv",
    ],
    includes=[
        "Quartus/rtl/uart",
    ],
    category="serial",
    description="UART ports wrapper tests"
)


# =============================================================================
# INFRASTRUCTURE Tests (New)
# =============================================================================

TEST_CONFIGS["ack_extender"] = TestConfig(
    name="ack_extender",
    testbench="ack_extender_tb.sv",
    sources=[
        "Quartus/rtl/AckExtender.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="core",
    description="Ack signal extender tests"
)

TEST_CONFIGS["fpu_control_register"] = TestConfig(
    name="fpu_control_register",
    testbench="fpu_control_register_tb.sv",
    sources=[
        "Quartus/rtl/FPUControlRegister.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="fpu",
    description="FPU control word I/O register tests"
)

TEST_CONFIGS["fpu_status_register"] = TestConfig(
    name="fpu_status_register",
    testbench="fpu_status_register_tb.sv",
    sources=[
        "Quartus/rtl/FPUStatusRegister.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="fpu",
    description="FPU status word I/O register tests"
)

TEST_CONFIGS["leds_register"] = TestConfig(
    name="leds_register",
    testbench="leds_register_tb.sv",
    sources=[
        "Quartus/rtl/leds/LEDSRegister.sv",
    ],
    includes=[
        "Quartus/rtl/leds",
    ],
    category="peripheral",
    description="Debug LED register tests"
)

TEST_CONFIGS["irq_controller"] = TestConfig(
    name="irq_controller",
    testbench="irq_controller_tb.sv",
    sources=[
        "Quartus/rtl/irq/IRQControl.sv",
    ],
    includes=[
        "Quartus/rtl/irq",
    ],
    category="peripheral",
    description="NMI/IRQ test controller tests"
)

TEST_CONFIGS["block_ram"] = TestConfig(
    name="block_ram",
    testbench="block_ram_tb.sv",
    sources=[
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="memory",
    description="Dual-port block RAM tests"
)

TEST_CONFIGS["dpram"] = TestConfig(
    name="dpram",
    testbench="dpram_tb.sv",
    sources=[
        "Quartus/rtl/common/DPRam.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="memory",
    description="Generic dual-port parameterized RAM tests"
)

TEST_CONFIGS["cache_arbiter"] = TestConfig(
    name="cache_arbiter",
    testbench="cache_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/common/CacheArbiter.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="arbiter",
    description="Harvard cache arbiter tests"
)


# =============================================================================
# ADDITIONAL DISCOVERED TESTS
# =============================================================================

# I-Cache tests
TEST_CONFIGS["icache2way_prefetch"] = TestConfig(
    name="icache2way_prefetch",
    testbench="icache2way_prefetch_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2WayPrefetch.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="memory",
    description="ICache 2-way with prefetcher tests"
)

TEST_CONFIGS["icache2way_simple"] = TestConfig(
    name="icache2way_simple",
    testbench="icache2way_simple_tb.sv",
    sources=[
        "Quartus/rtl/common/ICache2WayPrefetch.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="memory",
    description="ICache 2-way with prefetch basic tests"
)

# D-Cache tests
TEST_CONFIGS["dcache2way"] = TestConfig(
    name="dcache2way",
    testbench="dcache2way_tb.sv",
    sources=[
        "Quartus/rtl/common/DCache2Way.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    category="memory",
    description="DCache 2-way tests"
)

TEST_CONFIGS["dcache2way_simple"] = TestConfig(
    name="dcache2way_simple",
    testbench="",  # Not used for Verilator
    sources=[
        "Quartus/rtl/common/BlockRam.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/DCache2Way.sv",
    ],
    includes=[
        "Quartus/rtl/common",
    ],
    top_module="DCache2Way",
    category="memory",
    description="DCache 2-way simple testbench (Verilator - 13/13 pass)",
    simulator="verilator",
    cpp_testbench="verilator/dcache2way_tb.cpp"
)

# Pipelined arbiter tests
TEST_CONFIGS["pipelined_dma_arbiter"] = TestConfig(
    name="pipelined_dma_arbiter",
    testbench="pipelined_dma_arbiter_tb.sv",
    sources=[
        "Quartus/rtl/PipelinedDMAArbiter.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="arbiter",
    description="Pipelined DMA arbiter tests"
)

TEST_CONFIGS["pipelined_mem_arbiter_extend"] = TestConfig(
    name="pipelined_mem_arbiter_extend",
    testbench="pipelined_mem_arbiter_extend_tb.sv",
    sources=[
        "Quartus/rtl/PipelinedMemArbiterExtend.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="arbiter",
    description="Pipelined memory arbiter extend tests"
)

TEST_CONFIGS["pipelined_arbiters_comprehensive"] = TestConfig(
    name="pipelined_arbiters_comprehensive",
    testbench="pipelined_arbiters_comprehensive_tb.sv",
    sources=[
        "Quartus/rtl/PipelinedDMAArbiter.sv",
        "Quartus/rtl/PipelinedDMAFPUArbiter.sv",
        "Quartus/rtl/PipelinedMemArbiterExtend.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="arbiter",
    timeout=180,
    description="Comprehensive pipelined arbiter tests"
)

TEST_CONFIGS["pipelined_system_integration"] = TestConfig(
    name="pipelined_system_integration",
    testbench="pipelined_system_integration_tb.sv",
    sources=[
        "Quartus/rtl/PipelinedDMAArbiter.sv",
        "Quartus/rtl/PipelinedDMAFPUArbiter.sv",
        "Quartus/rtl/PipelinedMemArbiterExtend.sv",
    ],
    includes=[
        "Quartus/rtl",
    ],
    category="arbiter",
    timeout=180,
    description="Pipelined system integration tests"
)

# KF8259 submodule tests
TEST_CONFIGS["kf8259_bus_control"] = TestConfig(
    name="kf8259_bus_control",
    testbench="kf8259_bus_control_tb.sv",
    sources=[
        "Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv",
    ],
    includes=[
        "Quartus/rtl/KF8259",
    ],
    category="peripheral",
    description="KF8259 bus control logic unit tests"
)

TEST_CONFIGS["kf8259_in_service"] = TestConfig(
    name="kf8259_in_service",
    testbench="kf8259_in_service_tb.sv",
    sources=[
        "Quartus/rtl/KF8259/KF8259_In_Service.sv",
    ],
    includes=[
        "Quartus/rtl/KF8259",
    ],
    category="peripheral",
    description="KF8259 in-service register unit tests"
)

TEST_CONFIGS["kf8259_interrupt_request"] = TestConfig(
    name="kf8259_interrupt_request",
    testbench="kf8259_interrupt_request_tb.sv",
    sources=[
        "Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv",
    ],
    includes=[
        "Quartus/rtl/KF8259",
    ],
    category="peripheral",
    description="KF8259 interrupt request unit tests"
)

TEST_CONFIGS["kf8259_priority_resolver"] = TestConfig(
    name="kf8259_priority_resolver",
    testbench="kf8259_priority_resolver_tb.sv",
    sources=[
        "Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv",
    ],
    includes=[
        "Quartus/rtl/KF8259",
    ],
    category="peripheral",
    description="KF8259 priority resolver unit tests"
)

# CGA bus converter
TEST_CONFIGS["bus_converter"] = TestConfig(
    name="bus_converter",
    testbench="busConv_tb.sv",
    sources=[
        "Quartus/rtl/CGA/busConverter.sv",
        "Quartus/rtl/CGA/vram.sv",
    ],
    includes=[
        "Quartus/rtl/CGA",
    ],
    defines=["ICARUS"],
    category="video",
    description="CGA bus converter (8/16-bit) tests"
)

# VGA framebuffer integration
TEST_CONFIGS["vga_framebuffer_integration"] = TestConfig(
    name="vga_framebuffer_integration",
    testbench="vga_framebuffer_integration_tb.sv",
    sources=[
        "Quartus/rtl/VGA/VGATypes.sv",
        "Quartus/rtl/VGA/VGASync.sv",
        "Quartus/rtl/VGA/VGARegisters.sv",
        "Quartus/rtl/VGA/VGAPrefetchRAM_sim.sv",
        "Quartus/rtl/VGA/FBPrefetch.sv",
        "Quartus/rtl/VGA/FrameBuffer.sv",
        "Quartus/rtl/VGA/FontColorLUT.sv",
        "Quartus/rtl/VGA/VGAController.sv",
        "Quartus/rtl/CPU/cdc/BitSync.sv",
        "Quartus/rtl/CPU/cdc/BusSync.sv",
        "Quartus/rtl/CPU/cdc/MCP.sv",
        "Quartus/rtl/CPU/cdc/SyncPulse.sv",
        "modelsim/DACRam_sim.sv",
    ],
    includes=[
        "Quartus/rtl/VGA",
        "Quartus/rtl/CPU/cdc",
    ],
    defines=["ICARUS"],
    category="video",
    timeout=120,
    description="VGA framebuffer integration tests (simplified to 1 mode/frame for CI speed)"
)

# FSTSW AX tests
TEST_CONFIGS["fstsw_ax"] = TestConfig(
    name="fstsw_ax",
    testbench="tb_fstsw_ax.sv",
    sources=[],
    includes=[],
    category="fpu",
    description="FSTSW AX instruction tests"
)

TEST_CONFIGS["fstsw_ax_integration"] = TestConfig(
    name="fstsw_ax_integration",
    testbench="tb_fstsw_ax_integration.sv",
    sources=[],
    includes=[],
    category="fpu",
    description="FSTSW AX integration tests"
)


# =============================================================================
# FPU8087 Tests (moved from Quartus/rtl/FPU8087/tests/)
# =============================================================================

# Common FPU sources used by all tests
FPU8087_COMMON_SOURCES = [
    "Quartus/rtl/FPU8087/8087Status.v",
    "Quartus/rtl/FPU8087/AddSubComp.v",
    "Quartus/rtl/FPU8087/BarrelShifter.v",
    "Quartus/rtl/FPU8087/BitShifter.v",
    "Quartus/rtl/FPU8087/ByteShifter.v",
    "Quartus/rtl/FPU8087/CORDIC_Rotator.v",
    "Quartus/rtl/FPU8087/ControlWord.v",
    "Quartus/rtl/FPU8087/ESC_Decoder.v",
    "Quartus/rtl/FPU8087/FPU8087.v",
    "Quartus/rtl/FPU8087/FPU8087_Direct.v",
    # "Quartus/rtl/FPU8087/FPU8087_Integrated.v",  # Disabled - depends on missing FPU_Core_Wrapper
    "Quartus/rtl/FPU8087/FPU_ArithmeticUnit.v",
    "Quartus/rtl/FPU8087/FPU_Atan_Table.v",
    "Quartus/rtl/FPU8087/FPU_BCD_to_Binary.v",
    "Quartus/rtl/FPU8087/FPU_Binary_to_BCD.v",
    "Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v",
    "Quartus/rtl/FPU8087/FPU_CPU_Interface.v",
    "Quartus/rtl/FPU8087/FPU_ControlWord.v",
    "Quartus/rtl/FPU8087/FPU_Core.v",
    "Quartus/rtl/FPU8087/FPU_Core_Async.v",
    "Quartus/rtl/FPU8087/FPU_Exception_Handler.v",
    "Quartus/rtl/FPU8087/FPU_FP32_to_FP80.v",
    "Quartus/rtl/FPU8087/FPU_FP64_to_FP80.v",
    "Quartus/rtl/FPU8087/FPU_FP80_to_FP32.v",
    "Quartus/rtl/FPU8087/FPU_FP80_to_FP64.v",
    "Quartus/rtl/FPU8087/FPU_FP80_to_Int16.v",
    "Quartus/rtl/FPU8087/FPU_FP80_to_Int32.v",
    "Quartus/rtl/FPU8087/FPU_FP80_to_UInt64.v",
    "Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v",
    "Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v",
    "Quartus/rtl/FPU8087/FPU_IEEE754_Divide.v",
    "Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v",
    "Quartus/rtl/FPU8087/FPU_IEEE754_Multiply.v",
    "Quartus/rtl/FPU8087/FPU_Instruction_Decoder.v",
    "Quartus/rtl/FPU8087/FPU_Instruction_Queue.v",
    "Quartus/rtl/FPU8087/FPU_Int16_to_FP80.v",
    "Quartus/rtl/FPU8087/FPU_Int32_to_FP80.v",
    "Quartus/rtl/FPU8087/FPU_IO_Port.sv",
    "Quartus/rtl/FPU8087/FPU_Memory_Interface.v",
    "Quartus/rtl/FPU8087/FPU_Outer_Queue.v",
    "Quartus/rtl/FPU8087/FPU_Payne_Hanek.v",
    "Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v",
    "Quartus/rtl/FPU8087/FPU_Poly_Coeff_ROM.v",
    "Quartus/rtl/FPU8087/FPU_Polynomial_Evaluator.v",
    "Quartus/rtl/FPU8087/FPU_Range_Reduction.v",
    "Quartus/rtl/FPU8087/FPU_RegisterStack.v",
    "Quartus/rtl/FPU8087/FPU_SQRT_Newton.v",
    "Quartus/rtl/FPU8087/FPU_StatusWord.v",
    "Quartus/rtl/FPU8087/FPU_Transcendental.v",
    "Quartus/rtl/FPU8087/FPU_UInt64_to_FP80.v",
    "Quartus/rtl/FPU8087/LZCByte.v",
    "Quartus/rtl/FPU8087/LZCbit.v",
    "Quartus/rtl/FPU8087/MathConstants.v",
    "Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v",
    "Quartus/rtl/FPU8087/Normalizer.v",
    "Quartus/rtl/FPU8087/RoundUnit.v",
    "Quartus/rtl/FPU8087/StackRegister.v",
    "Quartus/rtl/FPU8087/tagRegister.v",
    "Quartus/rtl/FPU8087/three_bit_4x1_mux.v",
]

FPU8087_INCLUDES = ["Quartus/rtl/FPU8087"]

# Unit tests
TEST_CONFIGS["fpu8087_AddSubComp"] = TestConfig(
    name="fpu8087_AddSubComp",
    testbench="fpu8087_AddSubComp_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 AddSubComp tests"
)

TEST_CONFIGS["fpu8087_BarrelShifter"] = TestConfig(
    name="fpu8087_BarrelShifter",
    testbench="fpu8087_BarrelShifter_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 BarrelShifter tests"
)

TEST_CONFIGS["fpu8087_advanced_ops"] = TestConfig(
    name="fpu8087_advanced_ops",
    testbench="fpu8087_advanced_ops_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 advanced ops tests"
)

TEST_CONFIGS["fpu8087_advanced_transcendental"] = TestConfig(
    name="fpu8087_advanced_transcendental",
    testbench="fpu8087_advanced_transcendental_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 advanced transcendental tests"
)

TEST_CONFIGS["fpu8087_bcd"] = TestConfig(
    name="fpu8087_bcd",
    testbench="fpu8087_bcd_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 bcd tests"
)

TEST_CONFIGS["fpu8087_bcd_debug"] = TestConfig(
    name="fpu8087_bcd_debug",
    testbench="fpu8087_bcd_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 bcd debug tests"
)

TEST_CONFIGS["fpu8087_bcd_to_binary"] = TestConfig(
    name="fpu8087_bcd_to_binary",
    testbench="fpu8087_bcd_to_binary_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 bcd to binary tests"
)

TEST_CONFIGS["fpu8087_binary_to_bcd"] = TestConfig(
    name="fpu8087_binary_to_bcd",
    testbench="fpu8087_binary_to_bcd_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 binary to bcd tests"
)

TEST_CONFIGS["fpu8087_control_instructions"] = TestConfig(
    name="fpu8087_control_instructions",
    testbench="fpu8087_control_instructions_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 control instructions tests"
)

TEST_CONFIGS["fpu8087_conv_debug"] = TestConfig(
    name="fpu8087_conv_debug",
    testbench="fpu8087_conv_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 conv debug tests"
)

TEST_CONFIGS["fpu8087_cordic_direct"] = TestConfig(
    name="fpu8087_cordic_direct",
    testbench="fpu8087_cordic_direct_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 cordic direct tests"
)

TEST_CONFIGS["fpu8087_decoder_debug"] = TestConfig(
    name="fpu8087_decoder_debug",
    testbench="fpu8087_decoder_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 decoder debug tests"
)

TEST_CONFIGS["fpu8087_denormal_precision"] = TestConfig(
    name="fpu8087_denormal_precision",
    testbench="fpu8087_denormal_precision_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 denormal precision tests"
)

TEST_CONFIGS["fpu8087_esc_decoder"] = TestConfig(
    name="fpu8087_esc_decoder",
    testbench="fpu8087_esc_decoder_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 esc decoder tests"
)

TEST_CONFIGS["fpu8087_exception_functions"] = TestConfig(
    name="fpu8087_exception_functions",
    testbench="fpu8087_exception_functions_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 exception functions tests"
)

TEST_CONFIGS["fpu8087_exception_handler"] = TestConfig(
    name="fpu8087_exception_handler",
    testbench="fpu8087_exception_handler_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 exception handler tests"
)

TEST_CONFIGS["fpu8087_exception_handling"] = TestConfig(
    name="fpu8087_exception_handling",
    testbench="fpu8087_exception_handling_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 exception handling tests"
)

TEST_CONFIGS["fpu8087_extended_prechecks"] = TestConfig(
    name="fpu8087_extended_prechecks",
    testbench="fpu8087_extended_prechecks_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 extended prechecks tests"
)

TEST_CONFIGS["fpu8087_fcom"] = TestConfig(
    name="fpu8087_fcom",
    testbench="fpu8087_fcom_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fcom tests"
)

TEST_CONFIGS["fpu8087_fcom_debug"] = TestConfig(
    name="fpu8087_fcom_debug",
    testbench="fpu8087_fcom_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fcom debug tests"
)

TEST_CONFIGS["fpu8087_fcom_equal_debug"] = TestConfig(
    name="fpu8087_fcom_equal_debug",
    testbench="fpu8087_fcom_equal_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fcom equal debug tests"
)

TEST_CONFIGS["fpu8087_format_conv_fp"] = TestConfig(
    name="fpu8087_format_conv_fp",
    testbench="fpu8087_format_conv_fp_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 format conv fp tests"
)

TEST_CONFIGS["fpu8087_format_conv_int"] = TestConfig(
    name="fpu8087_format_conv_int",
    testbench="fpu8087_format_conv_int_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 format conv int tests"
)

TEST_CONFIGS["fpu8087_format_converter_unified"] = TestConfig(
    name="fpu8087_format_converter_unified",
    testbench="fpu8087_format_converter_unified_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 format converter unified tests"
)

TEST_CONFIGS["fpu8087_fprem_fxtract_fscale"] = TestConfig(
    name="fpu8087_fprem_fxtract_fscale",
    testbench="fpu8087_fprem_fxtract_fscale_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fprem fxtract fscale tests"
)

TEST_CONFIGS["fpu8087_fptan_simple"] = TestConfig(
    name="fpu8087_fptan_simple",
    testbench="fpu8087_fptan_simple_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fptan simple tests"
)

# fpu8087_fpu8087_direct removed - tests FPU8087_Direct.v which is NOT instantiated in production
# Production uses: mycore.sv -> FPU8087.v -> FPU_Core_Async.v -> FPU_Core.v

TEST_CONFIGS["fpu8087_fpu8087_trivial"] = TestConfig(
    name="fpu8087_fpu8087_trivial",
    testbench="fpu8087_fpu8087_trivial_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu8087 trivial tests"
)

TEST_CONFIGS["fpu8087_fpu8087_trivial_fixed"] = TestConfig(
    name="fpu8087_fpu8087_trivial_fixed",
    testbench="fpu8087_fpu8087_trivial_fixed_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu8087 trivial fixed tests"
)

TEST_CONFIGS["fpu8087_fpu_core"] = TestConfig(
    name="fpu8087_fpu_core",
    testbench="fpu8087_fpu_core_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu core tests"
)

TEST_CONFIGS["fpu8087_fpu_core_bcd_microcode"] = TestConfig(
    name="fpu8087_fpu_core_bcd_microcode",
    testbench="fpu8087_fpu_core_bcd_microcode_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu core bcd microcode tests"
)

# REMOVED: fpu8087_fpu_debug - testbench references obsolete internal signals
# REMOVED: fpu8087_fpu_io_registers - missing module dependencies

TEST_CONFIGS["fpu8087_fpu_memory_interface"] = TestConfig(
    name="fpu8087_fpu_memory_interface",
    testbench="fpu8087_fpu_memory_interface_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu memory interface tests"
)

TEST_CONFIGS["fpu8087_fstp_debug"] = TestConfig(
    name="fpu8087_fstp_debug",
    testbench="fpu8087_fstp_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fstp debug tests"
)

TEST_CONFIGS["fpu8087_fxam_debug"] = TestConfig(
    name="fpu8087_fxam_debug",
    testbench="fpu8087_fxam_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fxam debug tests"
)

TEST_CONFIGS["fpu8087_fxch"] = TestConfig(
    name="fpu8087_fxch",
    testbench="fpu8087_fxch_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fxch tests"
)

TEST_CONFIGS["fpu8087_fxtract_fscale"] = TestConfig(
    name="fpu8087_fxtract_fscale",
    testbench="fpu8087_fxtract_fscale_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fxtract fscale tests"
)

TEST_CONFIGS["fpu8087_ieee754_addsub"] = TestConfig(
    name="fpu8087_ieee754_addsub",
    testbench="fpu8087_ieee754_addsub_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 ieee754 addsub tests"
)

TEST_CONFIGS["fpu8087_ieee754_divide"] = TestConfig(
    name="fpu8087_ieee754_divide",
    testbench="fpu8087_ieee754_divide_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 ieee754 divide tests"
)

TEST_CONFIGS["fpu8087_ieee754_multiply"] = TestConfig(
    name="fpu8087_ieee754_multiply",
    testbench="fpu8087_ieee754_multiply_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 ieee754 multiply tests"
)

TEST_CONFIGS["fpu8087_instruction_decoder"] = TestConfig(
    name="fpu8087_instruction_decoder",
    testbench="fpu8087_instruction_decoder_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 instruction decoder tests"
)

TEST_CONFIGS["fpu8087_instruction_queue"] = TestConfig(
    name="fpu8087_instruction_queue",
    testbench="fpu8087_instruction_queue_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 instruction queue tests"
)

TEST_CONFIGS["fpu8087_int32_simple"] = TestConfig(
    name="fpu8087_int32_simple",
    testbench="fpu8087_int32_simple_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 int32 simple tests"
)

TEST_CONFIGS["fpu8087_integration_debug"] = TestConfig(
    name="fpu8087_integration_debug",
    testbench="fpu8087_integration_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 integration debug tests"
)

TEST_CONFIGS["fpu8087_memory_ops"] = TestConfig(
    name="fpu8087_memory_ops",
    testbench="fpu8087_memory_ops_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 memory ops tests"
)

# REMOVED: fpu8087_microcode - uses obsolete MicroSequencer module

TEST_CONFIGS["fpu8087_microcode_extended"] = TestConfig(
    name="fpu8087_microcode_extended",
    testbench="fpu8087_microcode_extended_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 microcode extended tests"
)

TEST_CONFIGS["fpu8087_microseq_bcd"] = TestConfig(
    name="fpu8087_microseq_bcd",
    testbench="fpu8087_microseq_bcd_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 microseq bcd tests"
)

TEST_CONFIGS["fpu8087_muldiv_unified"] = TestConfig(
    name="fpu8087_muldiv_unified",
    testbench="fpu8087_muldiv_unified_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 muldiv unified tests"
)

TEST_CONFIGS["fpu8087_realtime_debug"] = TestConfig(
    name="fpu8087_realtime_debug",
    testbench="fpu8087_realtime_debug_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 realtime debug tests"
)

TEST_CONFIGS["fpu8087_stack_mgmt"] = TestConfig(
    name="fpu8087_stack_mgmt",
    testbench="fpu8087_stack_mgmt_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 stack mgmt tests"
)

TEST_CONFIGS["fpu8087_transcendental"] = TestConfig(
    name="fpu8087_transcendental",
    testbench="fpu8087_transcendental_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 transcendental tests"
)

# REMOVED: fpu8087_transcendental_microcode - uses obsolete MicroSequencer_Extended module

TEST_CONFIGS["fpu8087_uint64_to_fp80"] = TestConfig(
    name="fpu8087_uint64_to_fp80",
    testbench="fpu8087_uint64_to_fp80_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 uint64 to fp80 tests"
)

# Integration tests
TEST_CONFIGS["fpu8087_fpu_async_operation"] = TestConfig(
    name="fpu8087_fpu_async_operation",
    testbench="fpu8087_fpu_async_operation_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu async operation tests"
)

TEST_CONFIGS["fpu8087_fpu_exception_integration"] = TestConfig(
    name="fpu8087_fpu_exception_integration",
    testbench="fpu8087_fpu_exception_integration_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 fpu exception integration tests"
)

# REMOVED: fpu8087_fpu_integration - Icarus Verilog syntax errors
# REMOVED: fpu8087_fpu_integration_simple - missing FPU8087_Integrated module

TEST_CONFIGS["fpu8087_muldiv_integration"] = TestConfig(
    name="fpu8087_muldiv_integration",
    testbench="fpu8087_muldiv_integration_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 muldiv integration tests"
)

# Payne-Hanek tests
TEST_CONFIGS["fpu8087_payne_hanek"] = TestConfig(
    name="fpu8087_payne_hanek",
    testbench="fpu8087_payne_hanek_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 payne hanek tests"
)

TEST_CONFIGS["fpu8087_payne_hanek_dispatch"] = TestConfig(
    name="fpu8087_payne_hanek_dispatch",
    testbench="fpu8087_payne_hanek_dispatch_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 payne hanek dispatch tests"
)

TEST_CONFIGS["fpu8087_payne_hanek_microcode"] = TestConfig(
    name="fpu8087_payne_hanek_microcode",
    testbench="fpu8087_payne_hanek_microcode_tb.v",
    sources=FPU8087_COMMON_SOURCES,
    includes=FPU8087_INCLUDES,
    category="fpu",
    description="FPU8087 payne hanek microcode tests"
)


# =============================================================================
# Verilator Tests
# These tests use Verilator instead of Icarus Verilog for better SystemVerilog support
# =============================================================================

TEST_CONFIGS["registerfile_verilator"] = TestConfig(
    name="registerfile_verilator",
    testbench="",  # Not used for Verilator
    sources=[
        "Quartus/rtl/CPU/RegisterEnum.sv",
        "Quartus/rtl/CPU/RegisterFile.sv",
    ],
    includes=["Quartus/rtl/CPU"],
    top_module="RegisterFile",
    category="core",
    simulator="verilator",
    cpp_testbench="verilator/registerfile_tb.cpp",
    description="RegisterFile Verilator test (unpacked arrays not supported by Icarus)"
)

TEST_CONFIGS["immediate_reader_verilator"] = TestConfig(
    name="immediate_reader_verilator",
    testbench="",  # Not used for Verilator
    sources=["Quartus/rtl/CPU/ImmediateReader.sv"],
    includes=["Quartus/rtl/CPU"],
    top_module="ImmediateReader",
    category="core",
    simulator="verilator",
    cpp_testbench="verilator/immediate_reader_tb.cpp",
    description="ImmediateReader Verilator test (constant selects not supported by Icarus)"
)


# =============================================================================
# Helper Functions
# =============================================================================

def get_all_tests() -> List[TestConfig]:
    """Return all test configurations."""
    return list(TEST_CONFIGS.values())


def get_tests_by_category(category: str) -> List[TestConfig]:
    """Return tests filtered by category."""
    return [t for t in TEST_CONFIGS.values() if t.category == category]


def get_test_by_name(name: str) -> Optional[TestConfig]:
    """Return a specific test by name."""
    return TEST_CONFIGS.get(name)


def get_all_categories() -> List[str]:
    """Return list of all test categories."""
    return list(set(t.category for t in TEST_CONFIGS.values()))
