module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- The Monster correspondence remains optional downstream x-pollination.
-- This capstone tracks only the finite non-Archimedean spectral closure.
--
-- Current source-exact state:
--
--   * function-level character action is owned;
--   * tau-odd preservation is owned;
--   * odd-character <-> tau-odd compiles from primitive half-turn + parity;
--   * the source product DFT is a valid unitary artifact but is rejected as the
--     literal odd-character transform;
--   * the correct odd-character transform reuses the existing half-size cyclic
--     DFT with diagonal omega^v modulation;
--   * the canonical two odd orbits compile from exact order/parity/cardinality;
--   * orbit signed cancellation compiles from the already-owned stronger
--     integer theorem `three_pow_two_pow` and ordinary finite-product algebra;
--   * the monomial matrix equality compiles from complete basis action using
--     existing finite matrix faithfulness.
--
-- Hence the only highest-alpha live source-specific front is the same-object
-- wiring between the literal Hadamard twisted coordinate carrier and the
-- tau-odd/odd-character function carrier.  Once that weld is instantiated, the
-- corrected DFT coordinates, spectrum, trace, and doubled-return power all fan
-- out downstream from the same object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OriginalGoalLeaf : Set where
  primitiveHalfTurnAtMinusOne : OriginalGoalLeaf
  oddCharacterTauOddIff : OriginalGoalLeaf
  instantiateCorrectOddCharacterDFT : OriginalGoalLeaf
  twistedCoordinateCharacterIdentification : OriginalGoalLeaf
  completeCharacterBasisActionEquality : OriginalGoalLeaf
  concreteDFTConjugatedEqualsMonomial : OriginalGoalLeaf
  arithmeticOddOrbitReceipts : OriginalGoalLeaf
  arithmeticOddOrbitChart : OriginalGoalLeaf
  orbitSumHalfPeriod : OriginalGoalLeaf
  negativeOrbitWeightSign : OriginalGoalLeaf
  orbitCancellationSumZero : OriginalGoalLeaf
  doubledReturnMinusTwo : OriginalGoalLeaf
  literalOneStepSpectrumUnion : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  owned : OriginalGoalStatus
  live : OriginalGoalStatus
  downstream : OriginalGoalStatus
  pruned : OriginalGoalStatus
  compiled : OriginalGoalStatus
  upstreamReusable : OriginalGoalStatus
  repoReusable : OriginalGoalStatus

leafStatus : OriginalGoalLeaf → OriginalGoalStatus
leafStatus primitiveHalfTurnAtMinusOne = upstreamReusable
leafStatus oddCharacterTauOddIff = compiled
leafStatus instantiateCorrectOddCharacterDFT = repoReusable
leafStatus twistedCoordinateCharacterIdentification = live
leafStatus completeCharacterBasisActionEquality = downstream
leafStatus concreteDFTConjugatedEqualsMonomial = compiled
leafStatus arithmeticOddOrbitReceipts = compiled
leafStatus arithmeticOddOrbitChart = compiled
leafStatus orbitSumHalfPeriod = compiled
leafStatus negativeOrbitWeightSign = compiled
leafStatus orbitCancellationSumZero = compiled
leafStatus doubledReturnMinusTwo = compiled
leafStatus literalOneStepSpectrumUnion = downstream

priority : List OriginalGoalLeaf
priority =
  twistedCoordinateCharacterIdentification ∷
  instantiateCorrectOddCharacterDFT ∷
  completeCharacterBasisActionEquality ∷
  literalOneStepSpectrumUnion ∷
  []

record SharedWeldFanout : Set where
  constructor sharedWeldFanout
  field
    correctedOddCharacterRechartFeedsSpatialSpectrum : Bool
    correctedOddCharacterRechartFeedsSpatialTrace : Bool
    correctedOddCharacterRechartFeedsSpatialPower : Bool
    equalityOnBasisCompilesLiteralMatrixEquality : Bool
    signedOrbitLaneIndependentOfSpatialRechart : Bool
    canonicalOrbitLaneIndependentOfSpatialRechart : Bool
    threeIndependentMatrixWeldsShouldBeSearched : Bool

canonicalSharedWeldFanout : SharedWeldFanout
canonicalSharedWeldFanout =
  sharedWeldFanout true true true true true true false

record OriginalGoalBoundary : Set where
  constructor originalGoalBoundary
  field
    functionLevelCharacterActionOwned : Bool
    tauOddPreservationOwned : Bool
    finiteMatrixBasisFaithfulnessOwned : Bool
    monomialPowerCalculusOwned : Bool
    orbitOrderOwned : Bool
    oddCardinalityOwned : Bool
    conditionalOrbitMagnitudeOwned : Bool
    conditionalPairedProductOwned : Bool
    concreteHadamardSplitOwned : Bool
    sourceProductDFTInfrastructureOwned : Bool
    determinantTowerFactorizationOwned : Bool

    sourceProductDFTIsOddCharacterTransform : Bool
    halfPeriodMathlibRouteAvailable : Bool
    oddCharacterTauOddIffCompilesFromHalfPeriod : Bool
    correctedOddCharacterDFTUsesExistingDFTTheory : Bool
    correctedOddCharacterDFTNeedsNewGenericFourierLibrary : Bool
    canonicalOddOrbitPackageCompilesFromExistingArithmetic : Bool
    strongThreePowerOddCoefficientOwned : Bool
    orbitSumHalfPeriodCompilesFromStrongThreePower : Bool
    negativeOrbitWeightSignCompilesFromOrbitSum : Bool
    orbitCancellationCompiles : Bool
    concreteMonomialEqualityCompilesFromBasisAction : Bool
    explicitPhaseValuesRequiredForMinusTwo : Bool
    doubledReturnMinusTwoCompilesFromCancellationProduct : Bool
    literalSpectrumTowerOwned : Bool

    monsterCorrespondenceRequiredForSpectralClosure : Bool
    finalMagnitudeHypothesisMayCloseItsOwnProducerPath : Bool

canonicalOriginalGoalBoundary : OriginalGoalBoundary
canonicalOriginalGoalBoundary =
  originalGoalBoundary
    true true true true true true true true true true true
    false true true true false true true true true true true false true false
    false false

currentProductDFTDoesNotCloseCharacterWeld :
  OriginalGoalBoundary.sourceProductDFTIsOddCharacterTransform
    canonicalOriginalGoalBoundary
  ≡ false
currentProductDFTDoesNotCloseCharacterWeld = refl

correctedDFTReusesExistingTheory :
  OriginalGoalBoundary.correctedOddCharacterDFTUsesExistingDFTTheory
    canonicalOriginalGoalBoundary
  ≡ true
correctedDFTReusesExistingTheory = refl

newFourierLibraryPruned :
  OriginalGoalBoundary.correctedOddCharacterDFTNeedsNewGenericFourierLibrary
    canonicalOriginalGoalBoundary
  ≡ false
newFourierLibraryPruned = refl

canonicalOddOrbitNowCompiled :
  leafStatus arithmeticOddOrbitReceipts ≡ compiled
canonicalOddOrbitNowCompiled = refl

orbitSumNowCompiled :
  leafStatus orbitSumHalfPeriod ≡ compiled
orbitSumNowCompiled = refl

signedCancellationNowCompiled :
  leafStatus orbitCancellationSumZero ≡ compiled
signedCancellationNowCompiled = refl

minusTwoNowCompiled :
  leafStatus doubledReturnMinusTwo ≡ compiled
minusTwoNowCompiled = refl

spatialCharacterWeldIsOnlyLiveFiniteCoreLeaf :
  leafStatus twistedCoordinateCharacterIdentification ≡ live
spatialCharacterWeldIsOnlyLiveFiniteCoreLeaf = refl

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
