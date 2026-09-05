module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- The Monster correspondence remains optional downstream x-pollination.
-- This capstone tracks only the finite non-Archimedean spectral closure.
--
-- New source correction:
-- source `Analysis/DFT.lean` owns a unitary F_(2^(n-2)) tensor I_2 after an
-- arbitrary cardinality product reindex.  That is NOT yet the odd-character
-- Fourier transform of the tau-antisymmetric twisted sector.
--
-- The natural odd-character kernel is
--
--   omega^((2j+1)v) = omega^v * (omega^2)^(jv),
--
-- i.e. a modulated 2^(n-1)-point DFT (up to row/column convention).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OriginalGoalLeaf : Set where
  primitiveHalfTurnAtMinusOne : OriginalGoalLeaf
  oddCharacterTauOddIff : OriginalGoalLeaf
  oddCharacterFourierRechart : OriginalGoalLeaf
  arithmeticOddOrbitReceipts : OriginalGoalLeaf
  arithmeticOddOrbitChart : OriginalGoalLeaf
  twistedCoordinateCharacterIdentification : OriginalGoalLeaf
  completeCharacterBasisActionEquality : OriginalGoalLeaf
  concreteDFTConjugatedEqualsMonomial : OriginalGoalLeaf
  canonicalTwoOddOrbitPackage : OriginalGoalLeaf
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

leafStatus : OriginalGoalLeaf → OriginalGoalStatus
leafStatus primitiveHalfTurnAtMinusOne = upstreamReusable
leafStatus oddCharacterTauOddIff = compiled
leafStatus oddCharacterFourierRechart = live
leafStatus arithmeticOddOrbitReceipts = live
leafStatus arithmeticOddOrbitChart = compiled
leafStatus twistedCoordinateCharacterIdentification = downstream
leafStatus completeCharacterBasisActionEquality = downstream
leafStatus concreteDFTConjugatedEqualsMonomial = compiled
leafStatus canonicalTwoOddOrbitPackage = downstream
leafStatus orbitCancellationSumZero = live
leafStatus doubledReturnMinusTwo = compiled
leafStatus literalOneStepSpectrumUnion = downstream

priority : List OriginalGoalLeaf
priority =
  oddCharacterFourierRechart ∷
  arithmeticOddOrbitReceipts ∷
  orbitCancellationSumZero ∷
  twistedCoordinateCharacterIdentification ∷
  completeCharacterBasisActionEquality ∷
  literalOneStepSpectrumUnion ∷
  []

record SharedWeldFanout : Set where
  constructor sharedWeldFanout
  field
    oddCharacterRechartFeedsSpatialSpectrum : Bool
    oddCharacterRechartFeedsSpatialTrace : Bool
    oddCharacterRechartFeedsSpatialPower : Bool
    equalityOnBasisCompilesLiteralMatrixEquality : Bool
    threeIndependentMatrixWeldsShouldBeSearched : Bool

canonicalSharedWeldFanout : SharedWeldFanout
canonicalSharedWeldFanout =
  sharedWeldFanout true true true true false

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
    oddCharacterFourierRechartOwned : Bool
    arithmeticOrbitChartCompilesFromReceipts : Bool
    concreteMonomialEqualityCompilesFromBasisAction : Bool
    explicitPhaseValuesRequiredForMinusTwo : Bool
    orbitCancellationSumZeroOwned : Bool
    doubledReturnMinusTwoCompilesFromCancellationProduct : Bool
    literalSpectrumTowerOwned : Bool

    monsterCorrespondenceRequiredForSpectralClosure : Bool
    finalMagnitudeHypothesisMayCloseItsOwnProducerPath : Bool

canonicalOriginalGoalBoundary : OriginalGoalBoundary
canonicalOriginalGoalBoundary =
  originalGoalBoundary
    true true true true true true true true true true true
    false true true false true true false false true false
    false false

currentProductDFTDoesNotCloseCharacterWeld :
  OriginalGoalBoundary.sourceProductDFTIsOddCharacterTransform
    canonicalOriginalGoalBoundary
  ≡ false
currentProductDFTDoesNotCloseCharacterWeld = refl

oddTauOddIffIsNoLongerPrimitiveSearchLeaf :
  leafStatus oddCharacterTauOddIff ≡ compiled
oddTauOddIffIsNoLongerPrimitiveSearchLeaf = refl

explicitComplexPhaseValuesNotRequired :
  OriginalGoalBoundary.explicitPhaseValuesRequiredForMinusTwo
    canonicalOriginalGoalBoundary
  ≡ false
explicitComplexPhaseValuesNotRequired = refl

minusTwoCompilesFromMinimalCancellation :
  OriginalGoalBoundary.doubledReturnMinusTwoCompilesFromCancellationProduct
    canonicalOriginalGoalBoundary
  ≡ true
minusTwoCompilesFromMinimalCancellation = refl

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
