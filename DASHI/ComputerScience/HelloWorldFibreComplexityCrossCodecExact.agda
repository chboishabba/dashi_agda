module DASHI.ComputerScience.HelloWorldFibreComplexityCrossCodecExact where

open import DASHI.Core.Prelude
open import Data.List using (length)

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.ComputerScience.HelloWorldEncodedWordMachineExact as Machine
import DASHI.ComputerScience.HelloWorldJacquardExact as JacquardHello
import DASHI.Codec.BalancedTritBitFibre as SupportSign
import DASHI.Codec.VerifiedFiniteTritCoder as FixedTwoBit
import DASHI.Foundations.TernaryNativeMinimalityExact as Native
import DASHI.Foundations.SSPTritCarrier as SSP

------------------------------------------------------------------------
-- HELLO WORLD COMPLEXITY ACROSS REPRESENTATION FIBRES
--
-- The same semantic computation carries multiple non-interchangeable costs.
-- This module deliberately does not pick one universal scalar complexity.
------------------------------------------------------------------------

helloWorldProgramCellCount : Nat
helloWorldProgramCellCount = length Machine.canonicalProgramMemory

helloWorldDataCellCount : Nat
helloWorldDataCellCount = length Machine.canonicalDataMemory

helloWorldTritCellCount : Nat
helloWorldTritCellCount = length JacquardHello.helloWorldTritStream

helloWorldSupportSignBitCost : Nat
helloWorldSupportSignBitCost =
  SupportSign.wordBitCost JacquardHello.helloWorldTritStream

fixedTwoBitCost : ∀ {A : Set} → List A → Nat
fixedTwoBitCost [] = 0
fixedTwoBitCost (_ ∷ xs) = suc (suc (fixedTwoBitCost xs))

helloWorldFixedTwoBitCost : Nat
helloWorldFixedTwoBitCost =
  fixedTwoBitCost JacquardHello.helloWorldTritStream

helloWorldProgramCellCountIsFourteen :
  helloWorldProgramCellCount ≡ 14
helloWorldProgramCellCountIsFourteen = refl

helloWorldDataCellCountIsThirteen :
  helloWorldDataCellCount ≡ 13
helloWorldDataCellCountIsThirteen = refl

helloWorldTritCellCountIsThree :
  helloWorldTritCellCount ≡ 3
helloWorldTritCellCountIsThree = refl

helloWorldSupportSignBitCostIsFive :
  helloWorldSupportSignBitCost ≡ 5
helloWorldSupportSignBitCostIsFive = refl

helloWorldFixedTwoBitCostIsSix :
  helloWorldFixedTwoBitCost ≡ 6
helloWorldFixedTwoBitCostIsSix = refl

canonicalHelloWorldComplexityProfile : Complexity.ComplexityProfile
canonicalHelloWorldComplexityProfile =
  Complexity.complexityProfile
    1
    helloWorldProgramCellCount
    helloWorldDataCellCount
    14
    2
    helloWorldTritCellCount
    14
    0

------------------------------------------------------------------------
-- Reuse exact ternary -> binary simulation rather than inventing another
-- codec.  This is a representation theorem, not an identification of ternary
-- semantics with Boolean geometry.
------------------------------------------------------------------------

nativeTritBinaryRoundTrip :
  (x : SSP.SSPTrit) →
  Native.decodeBinary (Native.encodeBinary x) ≡ x
nativeTritBinaryRoundTrip = Native.binarySimulationRoundTrip

record HelloWorldCrossCodecComplexityReceipt : Set where
  constructor helloWorldCrossCodecComplexityReceipt
  field
    programCells : Nat
    dataCells : Nat
    executionCycles : Nat
    semanticTritCells : Nat
    supportSignBits : Nat
    fixedTwoBitBits : Nat
    programCellsExact : programCells ≡ 14
    dataCellsExact : dataCells ≡ 13
    executionCyclesExact : executionCycles ≡ 14
    semanticTritCellsExact : semanticTritCells ≡ 3
    supportSignBitsExact : supportSignBits ≡ 5
    fixedTwoBitBitsExact : fixedTwoBitBits ≡ 6

canonicalHelloWorldCrossCodecComplexityReceipt :
  HelloWorldCrossCodecComplexityReceipt
canonicalHelloWorldCrossCodecComplexityReceipt =
  helloWorldCrossCodecComplexityReceipt
    helloWorldProgramCellCount
    helloWorldDataCellCount
    14
    helloWorldTritCellCount
    helloWorldSupportSignBitCost
    helloWorldFixedTwoBitCost
    helloWorldProgramCellCountIsFourteen
    helloWorldDataCellCountIsThirteen
    refl
    helloWorldTritCellCountIsThree
    helloWorldSupportSignBitCostIsFive
    helloWorldFixedTwoBitCostIsSix

record HelloWorldCrossCodecBoundary : Set where
  constructor helloWorldCrossCodecBoundary
  field
    supportSignAndFixedTwoBitCostsAreSameCoordinate : Bool
    lowerBitCostAutomaticallyMeansLowerRuntimeCost : Bool
    binarySimulationMakesTernarySemanticsBoolean : Bool
    complexityCoordinatesRemainFibreIndexed : Bool

canonicalHelloWorldCrossCodecBoundary : HelloWorldCrossCodecBoundary
canonicalHelloWorldCrossCodecBoundary =
  helloWorldCrossCodecBoundary false false false true
