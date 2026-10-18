module DASHI.ComputerScience.SchloeglFeyFPGASourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record FPGAResultReceipt : Set where
  constructor fpgaResultReceipt
  field
    source : String
    deviceFamily : String
    binaryCodedTernary : Bool
    lutOnlyImplementation : Bool
    carryChainImplementation : Bool
    reportedDigitWidthIndependentClockBehaviour : Bool
    reportedLutReductionPercentAgainstNaiveLUT : Nat
    resourceUseExceedsBinaryRCA : Bool
    gateLevelNetlistKernelFormalisedHere : Bool
open FPGAResultReceipt public

schloeglFeyReceipt : FPGAResultReceipt
schloeglFeyReceipt =
  fpgaResultReceipt
    "Schloegl and Fey, ARCS 2025 / LNCS 15839 (2026), DOI 10.1007/978-3-032-03281-2_3"
    "Xilinx/AMD UltraScale FPGA"
    true
    true
    true
    true
    50
    true
    false

record HardwareAuthorityBoundary : Set where
  constructor hardwareAuthorityBoundary
  field
    empiricalTimingIsAttributed : Bool
    timingClaimIsNotDerivedFromCodecAlone : Bool
    exactGateDepthNeedsNetlistOrCircuitOwner : Bool

canonicalHardwareAuthorityBoundary : HardwareAuthorityBoundary
canonicalHardwareAuthorityBoundary =
  hardwareAuthorityBoundary true true true
