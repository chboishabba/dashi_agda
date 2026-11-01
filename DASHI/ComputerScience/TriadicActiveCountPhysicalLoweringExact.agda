module DASHI.ComputerScience.TriadicActiveCountPhysicalLoweringExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.ComputerScience.TriadicSupportMaskPhysicalLoweringExact as Support

------------------------------------------------------------------------
-- SECOND CONCRETE PORTABLE CODEC OPERATION
--
-- The codec already owns `activeCount`: number of nonzero trits in a triple.
-- This module proves that the same quantity is the population count of the
-- projected three-bit support mask, then separates TOTAL count from PREFIX
-- count.  Total popcount determines sign-stream length; it does not determine
-- each active trit's sign-stream address.
------------------------------------------------------------------------

maskPopcount : MaskSign.Mask3 → Nat
maskPopcount MaskSign.mask000 = 0
maskPopcount MaskSign.mask001 = 1
maskPopcount MaskSign.mask010 = 1
maskPopcount MaskSign.mask011 = 2
maskPopcount MaskSign.mask100 = 1
maskPopcount MaskSign.mask101 = 2
maskPopcount MaskSign.mask110 = 2
maskPopcount MaskSign.mask111 = 3

activeCount-is-maskPopcount :
  (t : MaskSign.Triple Trit) →
  MaskSign.activeCount (MaskSign.encodeTriple t)
    ≡ maskPopcount (Support.supportMask t)
activeCount-is-maskPopcount (MaskSign.triple neg neg neg) = refl
activeCount-is-maskPopcount (MaskSign.triple neg neg zer) = refl
activeCount-is-maskPopcount (MaskSign.triple neg neg pos) = refl
activeCount-is-maskPopcount (MaskSign.triple neg zer neg) = refl
activeCount-is-maskPopcount (MaskSign.triple neg zer zer) = refl
activeCount-is-maskPopcount (MaskSign.triple neg zer pos) = refl
activeCount-is-maskPopcount (MaskSign.triple neg pos neg) = refl
activeCount-is-maskPopcount (MaskSign.triple neg pos zer) = refl
activeCount-is-maskPopcount (MaskSign.triple neg pos pos) = refl
activeCount-is-maskPopcount (MaskSign.triple zer neg neg) = refl
activeCount-is-maskPopcount (MaskSign.triple zer neg zer) = refl
activeCount-is-maskPopcount (MaskSign.triple zer neg pos) = refl
activeCount-is-maskPopcount (MaskSign.triple zer zer neg) = refl
activeCount-is-maskPopcount (MaskSign.triple zer zer zer) = refl
activeCount-is-maskPopcount (MaskSign.triple zer zer pos) = refl
activeCount-is-maskPopcount (MaskSign.triple zer pos neg) = refl
activeCount-is-maskPopcount (MaskSign.triple zer pos zer) = refl
activeCount-is-maskPopcount (MaskSign.triple zer pos pos) = refl
activeCount-is-maskPopcount (MaskSign.triple pos neg neg) = refl
activeCount-is-maskPopcount (MaskSign.triple pos neg zer) = refl
activeCount-is-maskPopcount (MaskSign.triple pos neg pos) = refl
activeCount-is-maskPopcount (MaskSign.triple pos zer neg) = refl
activeCount-is-maskPopcount (MaskSign.triple pos zer zer) = refl
activeCount-is-maskPopcount (MaskSign.triple pos zer pos) = refl
activeCount-is-maskPopcount (MaskSign.triple pos pos neg) = refl
activeCount-is-maskPopcount (MaskSign.triple pos pos zer) = refl
activeCount-is-maskPopcount (MaskSign.triple pos pos pos) = refl

------------------------------------------------------------------------
-- Prefix/sign-stream addressing.
------------------------------------------------------------------------

record SignStreamOffsets : Set where
  constructor sign-stream-offsets
  field
    beforeFirst : Nat
    beforeSecond : Nat
    beforeThird : Nat
    totalSigns : Nat
open SignStreamOffsets public

signOffsets : MaskSign.Triple MaskSign.FactorizedTrit → SignStreamOffsets
signOffsets (MaskSign.triple a b c) =
  sign-stream-offsets
    0
    (MaskSign.isActive a)
    (MaskSign.isActive a + MaskSign.isActive b)
    (MaskSign.activeCount (MaskSign.triple a b c))

signOffsetsForTrits : MaskSign.Triple Trit → SignStreamOffsets
signOffsetsForTrits t = signOffsets (MaskSign.encodeTriple t)

totalSigns-agrees-with-activeCount :
  (t : MaskSign.Triple Trit) →
  totalSigns (signOffsetsForTrits t)
    ≡ MaskSign.activeCount (MaskSign.encodeTriple t)
totalSigns-agrees-with-activeCount _ = refl

------------------------------------------------------------------------
-- Primary-source physical realization receipts.
------------------------------------------------------------------------

data CountLoweringKind : Set where
  scalarPackedPopcount x86POPCNT armSVECNTP cudaPOPC hipPOPC : CountLoweringKind

record CountLoweringReceipt : Set where
  constructor count-lowering-receipt
  field
    lowering : CountLoweringKind
    primaryOwner : String
    primaryLocator : String
    primitiveCountsSetOrActiveBits : Bool
    exactDASHIExecutableBinding : Bool
    exactInstructionSequencePaid : Bool
    exactOperandWidthPaid : Bool
    exactCrossBackendSemanticEquivalencePaid : Bool
    measuredLatencyPaid : Bool
    measuredEnergyPaid : Bool
open CountLoweringReceipt public

swarPopcountCandidate : CountLoweringReceipt
swarPopcountCandidate = count-lowering-receipt
  scalarPackedPopcount
  "DASHI codec substrate"
  "support mask is a packed scalar candidate; exact SWAR instruction sequence remains unpaid"
  true false false false true false false

x86PopcountCandidate : CountLoweringReceipt
x86PopcountCandidate = count-lowering-receipt
  x86POPCNT
  "Intel"
  "Intel 64/IA-32 Instruction Set Reference: POPCNT returns the number of source bits set to one"
  true false false false false false false

svePredicateCountCandidate : CountLoweringReceipt
svePredicateCountCandidate = count-lowering-receipt
  armSVECNTP
  "Arm"
  "Arm A-profile SVE instruction set: CNTP sets a scalar to the count of true predicate elements"
  true false false false false false false

cudaPopcountCandidate : CountLoweringReceipt
cudaPopcountCandidate = count-lowering-receipt
  cudaPOPC
  "NVIDIA"
  "CUDA __popc/__popcll count set bits; CUDA Best Practices documents __popc as a direct integer popcount primitive"
  true false false false false false false

hipPopcountCandidate : CountLoweringReceipt
hipPopcountCandidate = count-lowering-receipt
  hipPOPC
  "AMD"
  "HIP math/kernel API: __popc counts set bits in 32-bit input and __popcll in 64-bit input"
  true false false false false false false

------------------------------------------------------------------------
-- Reduction versus prefix: the next irreducible implementation fibre.
------------------------------------------------------------------------

data CountCase : Set where
  leftActiveCase rightActiveCase : CountCase

data TotalCountSurface : Set where
  oneActive : TotalCountSurface

data SignAddressReading : Set where
  firstLaneOwnsSign0 thirdLaneOwnsSign0 : SignAddressReading

projectTotalCount : CountCase → TotalCountSurface
projectTotalCount _ = oneActive

readSignAddress : CountCase → SignAddressReading
readSignAddress leftActiveCase = firstLaneOwnsSign0
readSignAddress rightActiveCase = thirdLaneOwnsSign0

-- Same total popcount, different positional/prefix answer.
data TotalPopcountImpliesPrefixAddress : Set where

totalPopcountDoesNotDeterminePrefix : TotalPopcountImpliesPrefixAddress → ⊥
totalPopcountDoesNotDeterminePrefix ()

record ActiveCountPhysicalResidual : Set where
  constructor active-count-physical-residual
  field
    semanticTotalCountFixed : Bool
    supportMaskReusePaid : Bool
    popcountPrimitiveAvailable : Bool
    prefixPositionStillNeeded : Bool
    laneOrderStillNeeded : Bool
    inactiveLanePolicyStillNeeded : Bool
    exactCompilerLoweringNeeded : Bool
    measuredPerformanceNeeded : Bool
open ActiveCountPhysicalResidual public

canonicalActiveCountResidual : ActiveCountPhysicalResidual
canonicalActiveCountResidual = active-count-physical-residual
  true true true true true true true true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PopcountImpliesPrefixScan : Set where
data SameActiveCountImpliesSameSignAddress : Set where
data HardwarePopcountImpliesCodecImplementation : Set where
data OneInstructionPopcountImpliesOneInstructionPrefix : Set where
data SameSetBitCountImpliesSameMask : Set where

popcountDoesNotCreatePrefixScan : PopcountImpliesPrefixScan → ⊥
popcountDoesNotCreatePrefixScan ()

sameCountDoesNotFixSignAddress : SameActiveCountImpliesSameSignAddress → ⊥
sameCountDoesNotFixSignAddress ()

hardwarePrimitiveDoesNotCreateCodecImplementation :
  HardwarePopcountImpliesCodecImplementation → ⊥
hardwarePrimitiveDoesNotCreateCodecImplementation ()

onePopcountInstructionDoesNotPayPrefix :
  OneInstructionPopcountImpliesOneInstructionPrefix → ⊥
onePopcountInstructionDoesNotPayPrefix ()

sameCountDoesNotIdentifyMask : SameSetBitCountImpliesSameMask → ⊥
sameCountDoesNotIdentifyMask ()

record TriadicActiveCountPhysicalLoweringBoundary : Set where
  constructor triadic-active-count-physical-lowering-boundary
  field
    existingActiveCountReused : Bool
    activeCountEqualsSupportMaskPopcount : Bool
    totalSignLengthPaid : Bool
    perPositionPrefixOffsetsDefined : Bool
    x86PopcountSourcePaid : Bool
    svePredicateCountSourcePaid : Bool
    cudaPopcountSourcePaid : Bool
    hipPopcountSourcePaid : Bool
    totalCountDeterminesPrefixAddress : Bool
    exactCrossBackendExecutableBindingPaid : Bool
    physicalPerformanceComparisonPaid : Bool
open TriadicActiveCountPhysicalLoweringBoundary public

canonicalTriadicActiveCountPhysicalLoweringBoundary :
  TriadicActiveCountPhysicalLoweringBoundary
canonicalTriadicActiveCountPhysicalLoweringBoundary =
  triadic-active-count-physical-lowering-boundary
    true true true true true true true true false false false
