module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- The Monster correspondence remains optional downstream x-pollination.
-- This capstone tracks only the finite non-Archimedean spectral closure.
--
-- Current source-exact state:
--
--   * function-level character action is source-owned;
--   * tau-odd preservation is source-owned;
--   * odd-character <-> tau-odd compiles from primitive half-turn + parity;
--   * the source product DFT is unitary but rejected as the literal
--     odd-character transform;
--   * the corrected odd-character transform reuses the existing cyclic DFT
--     plus diagonal modulation;
--   * the binary-sheet half-function <-> tau-odd-function equivalence is owned;
--   * the generic twisted-restriction operator identity compiles to the shared
--     Core.Intertwiner interface;
--   * canonical odd orbits and signed return compile from existing arithmetic;
--   * literal monomial matrix equality compiles from complete basis action via
--     existing finite matrix faithfulness.
--
-- Therefore the only live finite-core task is now source instantiation:
-- identify the concrete ZMod 2 sheet representation and D'_matrix/twistedDirMatrix
-- definitions with the already-owned binary-sheet restriction compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OriginalGoalLeaf : Set where
  primitiveHalfTurnAtMinusOne : OriginalGoalLeaf
  oddCharacterTauOddIff : OriginalGoalLeaf
  instantiateCorrectOddCharacterDFT : OriginalGoalLeaf
  binarySheetTauOddEquivalence : OriginalGoalLeaf
  genericTwistedRestrictionIntertwiner : OriginalGoalLeaf
  instantiateConcreteSourceSheetAdapter : OriginalGoalLeaf
  composeRestrictionWithOddCharacterDFT : OriginalGoalLeaf
  completeCharacterBasisActionEquality : OriginalGoalLeaf
  concreteDFTConjugatedEqualsMonomial : OriginalGoalLeaf
  canonicalOddOrbitPackage : OriginalGoalLeaf
  orbitSumHalfPeriod : OriginalGoalLeaf
  orbitCancellationSumZero : OriginalGoalLeaf
  doubledReturnMinusTwo : OriginalGoalLeaf
  literalOneStepSpectrumUnion : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  owned : OriginalGoalStatus
  live : OriginalGoalStatus
  downstream : OriginalGoalStatus
  compiled : OriginalGoalStatus
  upstreamReusable : OriginalGoalStatus
  repoReusable : OriginalGoalStatus

leafStatus : OriginalGoalLeaf → OriginalGoalStatus
leafStatus primitiveHalfTurnAtMinusOne = upstreamReusable
leafStatus oddCharacterTauOddIff = compiled
leafStatus instantiateCorrectOddCharacterDFT = repoReusable
leafStatus binarySheetTauOddEquivalence = owned
leafStatus genericTwistedRestrictionIntertwiner = compiled
leafStatus instantiateConcreteSourceSheetAdapter = live
leafStatus composeRestrictionWithOddCharacterDFT = downstream
leafStatus completeCharacterBasisActionEquality = downstream
leafStatus concreteDFTConjugatedEqualsMonomial = compiled
leafStatus canonicalOddOrbitPackage = compiled
leafStatus orbitSumHalfPeriod = compiled
leafStatus orbitCancellationSumZero = compiled
leafStatus doubledReturnMinusTwo = compiled
leafStatus literalOneStepSpectrumUnion = downstream

priority : List OriginalGoalLeaf
priority =
  instantiateConcreteSourceSheetAdapter ∷
  composeRestrictionWithOddCharacterDFT ∷
  completeCharacterBasisActionEquality ∷
  literalOneStepSpectrumUnion ∷
  []

record SharedWeldFanout : Set where
  constructor sharedWeldFanout
  field
    oneConcreteSheetAdapterFeedsSpectrum : Bool
    oneConcreteSheetAdapterFeedsTrace : Bool
    oneConcreteSheetAdapterFeedsPower : Bool
    genericRestrictionIntertwinerReused : Bool
    equalityOnBasisCompilesLiteralMatrixEquality : Bool
    signedOrbitLaneAlreadyClosed : Bool
    canonicalOrbitLaneAlreadyClosed : Bool
    threeIndependentSpatialWeldsShouldBeSearched : Bool

canonicalSharedWeldFanout : SharedWeldFanout
canonicalSharedWeldFanout =
  sharedWeldFanout true true true true true true true false

record OriginalGoalBoundary : Set where
  constructor originalGoalBoundary
  field
    functionLevelCharacterActionOwned : Bool
    tauOddPreservationOwned : Bool
    finiteMatrixBasisFaithfulnessOwned : Bool
    monomialPowerCalculusOwned : Bool
    concreteHadamardSplitOwned : Bool
    sourceProductDFTInfrastructureOwned : Bool
    determinantTowerFactorizationOwned : Bool

    sourceProductDFTIsOddCharacterTransform : Bool
    oddCharacterTauOddIffCompiled : Bool
    correctedOddCharacterDFTUsesExistingDFTTheory : Bool
    binarySheetTauOddEquivalenceOwned : Bool
    genericTwistedRestrictionIntertwinerCompiled : Bool
    concreteSourceSheetAdapterOwned : Bool
    canonicalOddOrbitPackageCompiled : Bool
    orbitCancellationCompiled : Bool
    concreteMonomialEqualityCompilesFromBasisAction : Bool
    literalSpectrumTowerOwned : Bool

    monsterCorrespondenceRequiredForSpectralClosure : Bool
    finalMagnitudeHypothesisMayCloseItsOwnProducerPath : Bool

canonicalOriginalGoalBoundary : OriginalGoalBoundary
canonicalOriginalGoalBoundary =
  originalGoalBoundary
    true true true true true true true
    false true true true true false true true true false
    false false

currentProductDFTDoesNotCloseCharacterWeld :
  OriginalGoalBoundary.sourceProductDFTIsOddCharacterTransform
    canonicalOriginalGoalBoundary
  ≡ false
currentProductDFTDoesNotCloseCharacterWeld = refl

binarySheetEquivalenceIsOwned :
  OriginalGoalBoundary.binarySheetTauOddEquivalenceOwned
    canonicalOriginalGoalBoundary
  ≡ true
binarySheetEquivalenceIsOwned = refl

genericRestrictionCompilerIsOwned :
  OriginalGoalBoundary.genericTwistedRestrictionIntertwinerCompiled
    canonicalOriginalGoalBoundary
  ≡ true
genericRestrictionCompilerIsOwned = refl

concreteSourceSheetAdapterIsOnlyLiveFiniteCoreLeaf :
  leafStatus instantiateConcreteSourceSheetAdapter ≡ live
concreteSourceSheetAdapterIsOnlyLiveFiniteCoreLeaf = refl

signedCancellationNowCompiled :
  leafStatus orbitCancellationSumZero ≡ compiled
signedCancellationNowCompiled = refl

minusTwoNowCompiled :
  leafStatus doubledReturnMinusTwo ≡ compiled
minusTwoNowCompiled = refl

monsterIsOptionalForOriginalClosure :
  OriginalGoalBoundary.monsterCorrespondenceRequiredForSpectralClosure
    canonicalOriginalGoalBoundary
  ≡ false
monsterIsOptionalForOriginalClosure = refl

finalMagnitudeCannotSelfDischarge :
  OriginalGoalBoundary.finalMagnitudeHypothesisMayCloseItsOwnProducerPath
    canonicalOriginalGoalBoundary
  ≡ false
finalMagnitudeCannotSelfDischarge = refl
