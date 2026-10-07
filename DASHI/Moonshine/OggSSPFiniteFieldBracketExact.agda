module DASHI.Moonshine.OggSSPFiniteFieldBracketExact where

------------------------------------------------------------------------
-- NUMERICAL FINITE-FIELD / TRANSITION ATLAS FOR THE J369 / SSP15 SURFACE
--
-- Generated tables/plots are numerical evidence only.  They do not recognize
-- a DASHI carrier as a finite field from cardinality, orbit count, group size,
-- or visual similarity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Generated.OggSSPFiniteFieldBracketGenerated as Generated
import DASHI.Biology.FRACTRANSSPTransitionExact as Legacy

generatedFieldBracketRowCountIsSixteen : Generated.fieldBracketRowCount ≡ 16
generatedFieldBracketRowCountIsSixteen = refl

generated196831PrimalityScreenPassed : Generated.generatorPrime196831 ≡ true
generated196831PrimalityScreenPassed = refl

generated196830MultiplicativeNumerator : 196830 + 1 ≡ 196831
generated196830MultiplicativeNumerator = Generated.bulkMultiplicativeExact

generatedTenQuadraticOrbitNumerator : 2 * 10 ≡ 4 * 4 + 4
generatedTenQuadraticOrbitNumerator = Generated.tenQuadraticOrbitNumeratorExact

generatedFifteenQuadraticOrbitNumerator : 2 * 15 ≡ 5 * 5 + 5
generatedFifteenQuadraticOrbitNumerator = Generated.fifteenQuadraticOrbitNumeratorExact

generatedTwentyFourHasGF81OverGF3OrbitNumerator : 4 * 24 ≡ 2 * 3 + 9 + 81
generatedTwentyFourHasGF81OverGF3OrbitNumerator = Generated.twentyFourGF81OverGF3OrbitNumeratorExact

generatedTwentyFourHasGF64OverGF4OrbitNumerator : 3 * 24 ≡ 2 * 4 + 64
generatedTwentyFourHasGF64OverGF4OrbitNumerator = Generated.twentyFourGF64OverGF4OrbitNumeratorExact

------------------------------------------------------------------------
-- 1,330-state plot.
-- Weak compositions of mass 18 into four exponents give C(21,3)=1330.
-- The generator mirrors Legacy.firstEnabledStep and checks every target stays
-- in the mass-18 slice, hence one directed edge per generated source state.
------------------------------------------------------------------------

mass18WeakCompositionNumerator : 1330 * 6 ≡ 21 * 20 * 19
mass18WeakCompositionNumerator = Generated.mass18WeakCompositionNumeratorExact

generatedMass18NodeCount : Generated.legacyMass18NodeCount ≡ 1330
generatedMass18NodeCount = refl

generatedMass18EdgeCount : Generated.legacyMass18EdgeCount ≡ 1330
generatedMass18EdgeCount = refl

legacyFirstStepSameObject :
  Legacy.firstEnabledStep Legacy.canonicalPrimeState ≡ Legacy.firstCanonicalTransfer
legacyFirstStepSameObject = Legacy.canonicalPriorityUses47To59

legacyThreeStepOccupancyCycleReused :
  Legacy.exponent47 Legacy.thirdCanonicalTransfer ≡ 1
  × Legacy.exponent59 Legacy.thirdCanonicalTransfer ≡ 0
  × Legacy.exponent71 Legacy.thirdCanonicalTransfer ≡ 0
legacyThreeStepOccupancyCycleReused = Legacy.threeStepCycleReturnsOggOccupancy

------------------------------------------------------------------------
-- Screenshot comparison firewall.
-- The supplied screenshot also displays 1330 nodes / 1330 edges, but its 12
-- displacement vectors do not match the deterministic 37-column DASHI plot,
-- which has 233.  Same counts therefore do not identify the graph.
------------------------------------------------------------------------

generatedGridDisplacementVectorCount :
  Generated.legacyMass18GridDisplacementVectorCount ≡ 233
generatedGridDisplacementVectorCount = refl

generatedScreenshotTwelveVectorMatchRejected :
  Generated.screenshotTwelveVectorCountMatches ≡ false
generatedScreenshotTwelveVectorMatchRejected = refl

------------------------------------------------------------------------
-- Recognition payment contract.  Every finite-field/tower hit remains a
-- numerical candidate until the canonical action/orbit/stabilizer contract is
-- paid by an independent source-side construction.
------------------------------------------------------------------------

record RecognitionPayment : Set where
  constructor recognition-payment
  field
    objectMapPaid : Bool
    arrowMapPaid : Bool
    actionIntertwiningPaid : Bool
    orbitMapPaid : Bool
    representativeCompatibilityPaid : Bool
    stabilizerPreservationPaid : Bool
    stabilizerReflectionPaid : Bool
    pi0SemanticMatchPaid : Bool

open RecognitionPayment public

allNumericalFieldCandidatesUnpaid : RecognitionPayment
allNumericalFieldCandidatesUnpaid =
  recognition-payment false false false false false false false false

candidateRecognitionPayment : Nat → RecognitionPayment
candidateRecognitionPayment n = allNumericalFieldCandidatesUnpaid

data CardinalityMatchRecognizesField : Set where
data OrbitCountMatchRecognizesField : Set where
data PlotSimilarityRecognizesSameGraph : Set where
data Mass18LegacyProjectionRecognizesFullSignedFifteenLaneWeave : Set where

cardinalityMatchDoesNotRecognizeField : CardinalityMatchRecognizesField → ⊥
cardinalityMatchDoesNotRecognizeField ()

orbitCountMatchDoesNotRecognizeField : OrbitCountMatchRecognizesField → ⊥
orbitCountMatchDoesNotRecognizeField ()

plotSimilarityDoesNotRecognizeSameGraph : PlotSimilarityRecognizesSameGraph → ⊥
plotSimilarityDoesNotRecognizeSameGraph ()

legacyProjectionDoesNotRecognizeFullSignedWeave :
  Mass18LegacyProjectionRecognizesFullSignedFifteenLaneWeave → ⊥
legacyProjectionDoesNotRecognizeFullSignedWeave ()

record OggSSPFiniteFieldBracketBoundary : Set where
  constructor ogg-ssp-finite-field-bracket-boundary
  field
    generatedBracketTableOwned : Bool
    generatedCandidateRankingOwned : Bool
    generatedPlotsOwned : Bool
    legacyMass18TransitionAtlasOwned : Bool
    mass18ScreenshotNodeEdgeCountCoincidenceRecorded : Bool
    screenshotSameGraphClaimed : Bool
    t5ObjectSubfieldLatticeInferredFromCounts : Bool
    anyNumericalCandidateRecognized : Bool
    fullSignedFifteenLaneWeaveRecognizedByLegacyPlot : Bool

canonicalOggSSPFiniteFieldBracketBoundary : OggSSPFiniteFieldBracketBoundary
canonicalOggSSPFiniteFieldBracketBoundary =
  ogg-ssp-finite-field-bracket-boundary
    true true true true true
    false false false false
