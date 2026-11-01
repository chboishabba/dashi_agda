module DASHI.ComputerScience.TekumTriadicABIBackendBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Codec.TriadicPAdicCodec as PAdic
import DASHI.ComputerScience.TriadicByteABIRoadmapWeldExact as ABI
import DASHI.ComputerScience.TernarySignedDigitBinaryCodeBridgeExact as TwoBit
import DASHI.ComputerScience.SchloeglFeyFPGASourceBoundaryExact as FPGA

------------------------------------------------------------------------
-- Tekum reaches existing implementation boundaries without promoting them.

Pack5Obligation : Set₁
Pack5Obligation = PAdic.Pack5Contract

ThreeTritReference : Set
ThreeTritReference = ABI.ThreeTritReference

ThreeTritByteCarrier : Set
ThreeTritByteCarrier = ABI.ThreeTritByteCarrier

record TekumBackendBoundary : Set where
  constructor tekumBackendBoundary
  field
    twoBitTritCodecPaid : Bool
    triadicThreeTritByteReferencePaid : Bool
    pAdicFiveTritPackContractReused : Bool
    rustU8BindingPaidHere : Bool
    swarRuntimePaidHere : Bool
    fpgaNetlistPaidHere : Bool
    schloeglFeyEmpiricalBoundaryRetained : Bool

canonicalTekumBackendBoundary : TekumBackendBoundary
canonicalTekumBackendBoundary =
  tekumBackendBoundary true true true false false false true
