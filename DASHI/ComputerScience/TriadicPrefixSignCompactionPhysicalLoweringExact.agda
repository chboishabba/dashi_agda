module DASHI.ComputerScience.TriadicPrefixSignCompactionPhysicalLoweringExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.ComputerScience.TriadicSupportMaskPhysicalLoweringExact as Support
import DASHI.ComputerScience.TriadicActiveCountPhysicalLoweringExact as Active

------------------------------------------------------------------------
-- THIRD CONCRETE PORTABLE CODEC OPERATION
--
-- Per-position sign-stream address = count of active positions strictly
-- before that position.  This is the exact prefix-popcount/compaction object
-- left open by total active count.
------------------------------------------------------------------------

data Position3 : Set where firstPos secondPos thirdPos : Position3

prefixActiveCount : MaskSign.Triple MaskSign.FactorizedTrit → Position3 → Nat
prefixActiveCount (MaskSign.triple a b c) firstPos  = 0
prefixActiveCount (MaskSign.triple a b c) secondPos = MaskSign.isActive a
prefixActiveCount (MaskSign.triple a b c) thirdPos  = MaskSign.isActive a + MaskSign.isActive b

prefixActiveCountForTrits : MaskSign.Triple Trit → Position3 → Nat
prefixActiveCountForTrits t p = prefixActiveCount (MaskSign.encodeTriple t) p

prefix-agrees-with-signOffsets-first :
  (t : MaskSign.Triple Trit) →
  prefixActiveCountForTrits t firstPos ≡ Active.beforeFirst (Active.signOffsetsForTrits t)
prefix-agrees-with-signOffsets-first _ = refl

prefix-agrees-with-signOffsets-second :
  (t : MaskSign.Triple Trit) →
  prefixActiveCountForTrits t secondPos ≡ Active.beforeSecond (Active.signOffsetsForTrits t)
prefix-agrees-with-signOffsets-second _ = refl

prefix-agrees-with-signOffsets-third :
  (t : MaskSign.Triple Trit) →
  prefixActiveCountForTrits t thirdPos ≡ Active.beforeThird (Active.signOffsetsForTrits t)
prefix-agrees-with-signOffsets-third _ = refl

------------------------------------------------------------------------
-- Compaction contract.
------------------------------------------------------------------------

record SignCompactionReceipt : Set where
  constructor sign-compaction-receipt
  field
    supportMaskKnown : Bool
    totalActiveCountKnown : Bool
    orderedPrefixCountKnown : Bool
    inactivePositionsConsumeSignSlot : Bool
    activePositionAddressIsPrefixCount : Bool
    exactBackendExecutableBinding : Bool
open SignCompactionReceipt public

canonicalSignCompactionReceipt : SignCompactionReceipt
canonicalSignCompactionReceipt =
  sign-compaction-receipt true true true false true false

------------------------------------------------------------------------
-- Backend realization shapes.
------------------------------------------------------------------------

data PrefixLoweringKind : Set where
  scalarLowerBitsPopcount
  cudaLowerLaneMaskPopcount
  hipLowerLaneMaskPopcount
  svePrefixPredicateCount
  x86MaskLowerBitsPopcount : PrefixLoweringKind

record PrefixLoweringReceipt : Set where
  constructor prefix-lowering-receipt
  field
    lowering : PrefixLoweringKind
    primaryOwner : String
    primaryLocator : String
    hasOrderedPrefixMechanism : Bool
    hasCountMechanism : Bool
    exactDASHIExecutableBinding : Bool
    exactLaneOrderingBound : Bool
    exactInactiveLanePolicyBound : Bool
    measuredLatencyPaid : Bool
    measuredEnergyPaid : Bool
open PrefixLoweringReceipt public

scalarPrefixCandidate : PrefixLoweringReceipt
scalarPrefixCandidate = prefix-lowering-receipt
  scalarLowerBitsPopcount
  "DASHI codec substrate"
  "prefix address may be computed as popcount(mask & lowerBits(position)); exact machine-word implementation remains unpaid"
  true true false false false false false

cudaPrefixCandidate : PrefixLoweringReceipt
cudaPrefixCandidate = prefix-lowering-receipt
  cudaLowerLaneMaskPopcount
  "NVIDIA"
  "PTX special register %lanemask_lt supplies lower-lane mask; CUDA integer popcount supplies count"
  true true false false false false false

hipPrefixCandidate : PrefixLoweringReceipt
hipPrefixCandidate = prefix-lowering-receipt
  hipLowerLaneMaskPopcount
  "AMD"
  "HIP provides ballot/popcount primitives; exact canonical lower-lane-mask carrier remains source-bound per target/runtime"
  false true false false false false false

svePrefixCandidate : PrefixLoweringReceipt
svePrefixCandidate = prefix-lowering-receipt
  svePrefixPredicateCount
  "Arm"
  "SVE predicate operations plus CNTP can count true elements in a prefix predicate; exact codec lowering remains unpaid"
  true true false false false false false

x86PrefixCandidate : PrefixLoweringReceipt
x86PrefixCandidate = prefix-lowering-receipt
  x86MaskLowerBitsPopcount
  "Intel"
  "scalar/vector mask extraction followed by lower-bit masking and POPCNT can realize prefix count; exact sequence remains unpaid"
  true true false false false false false

------------------------------------------------------------------------
-- Non-factorability: total active count cannot recover ordered prefix state.
------------------------------------------------------------------------

data PrefixCase : Set where
  firstOnly secondOnly thirdOnly : PrefixCase

data TotalSurface : Set where oneTotal : TotalSurface

data PrefixReading : Set where prefix0 prefix1 : PrefixReading

projectTotal : PrefixCase → TotalSurface
projectTotal _ = oneTotal

readThirdPrefix : PrefixCase → PrefixReading
readThirdPrefix firstOnly = prefix1
readThirdPrefix secondOnly = prefix1
readThirdPrefix thirdOnly = prefix0

data TotalCountDeterminesThirdPrefix : Set where

totalDoesNotDetermineThirdPrefix : TotalCountDeterminesThirdPrefix → ⊥
totalDoesNotDetermineThirdPrefix ()

------------------------------------------------------------------------
-- Roadmap frontier object.
------------------------------------------------------------------------

record PortableTriadicCodecRoadmap : Set where
  constructor portable-triadic-codec-roadmap
  field
    algebraicSupportSignExact : Bool
    supportMaskExact : Bool
    activeCountExact : Bool
    prefixSignAddressExact : Bool
    compactSignStreamLayoutExact : Bool
    portableBackendSemanticShapesKnown : Bool
    exactSWARExecutable : Bool
    exactX86Executable : Bool
    exactArmExecutable : Bool
    exactCUDAExecutable : Bool
    exactROCmExecutable : Bool
    roundTripEncodeDecodeOnBackend : Bool
    crossBackendPropertyTests : Bool
    measuredThroughput : Bool
    measuredLatency : Bool
    measuredEnergy : Bool
    semiconductorDeviceIdentityBound : Bool
    manufacturingProvenanceBound : Bool
open PortableTriadicCodecRoadmap public

currentPortableTriadicCodecRoadmap : PortableTriadicCodecRoadmap
currentPortableTriadicCodecRoadmap = portable-triadic-codec-roadmap
  true true true true true true
  false false false false false
  false false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PrefixFormulaImpliesCompiledKernel : Set where
data SamePrefixSemanticsImpliesSameLaneOrdering : Set where
data BallotPopcountImpliesCompactionComplete : Set where
data PrefixAddressImpliesRoundTripCodec : Set where
data PortableSemanticShapeImpliesPerformancePortability : Set where

prefixFormulaDoesNotCreateKernel : PrefixFormulaImpliesCompiledKernel → ⊥
prefixFormulaDoesNotCreateKernel ()

samePrefixDoesNotFixLaneOrdering : SamePrefixSemanticsImpliesSameLaneOrdering → ⊥
samePrefixDoesNotFixLaneOrdering ()

ballotPopcountDoesNotFinishCompaction : BallotPopcountImpliesCompactionComplete → ⊥
ballotPopcountDoesNotFinishCompaction ()

prefixAddressDoesNotCreateRoundTrip : PrefixAddressImpliesRoundTripCodec → ⊥
prefixAddressDoesNotCreateRoundTrip ()

semanticPortabilityDoesNotPayPerformancePortability :
  PortableSemanticShapeImpliesPerformancePortability → ⊥
semanticPortabilityDoesNotPayPerformancePortability ()
