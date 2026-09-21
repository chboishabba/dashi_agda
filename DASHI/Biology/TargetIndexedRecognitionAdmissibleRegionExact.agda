module DASHI.Biology.TargetIndexedRecognitionAdmissibleRegionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Biology.TargetIndexedRecognitionGeometryExact as Geometry

------------------------------------------------------------------------
-- NON-COMPENSATORY TARGET-INDEXED ADMISSIBLE REGIONS
--
-- A weighted mismatch score is useful but can hide a fatal mismatch:
-- excellent agreement on seven coordinates can numerically compensate for
-- failure on one coordinate even when the biological target cannot.
--
-- This owner therefore adds coordinate-wise tolerances.  A real target may
-- use a weighted score, a hard admissible box, or both.
------------------------------------------------------------------------

record RecognitionTolerance : Set where
  constructor recognitionTolerance
  field
    chargeTolerance : Nat
    sizeShapeTolerance : Nat
    donorAcceptorTolerance : Nat
    localGeometryTolerance : Nat
    coordinationTolerance : Nat
    solvationTolerance : Nat
    conformationTolerance : Nat
    kineticTolerance : Nat

open RecognitionTolerance public

record WithinTolerance
    (tolerance : RecognitionTolerance)
    (mismatch : Geometry.RecognitionMismatch) : Set where
  constructor withinTolerance
  field
    chargeWithin :
      Geometry.chargeMismatch mismatch ≤ chargeTolerance tolerance

    sizeShapeWithin :
      Geometry.sizeShapeMismatch mismatch ≤ sizeShapeTolerance tolerance

    donorAcceptorWithin :
      Geometry.donorAcceptorMismatch mismatch ≤ donorAcceptorTolerance tolerance

    localGeometryWithin :
      Geometry.localGeometryMismatch mismatch ≤ localGeometryTolerance tolerance

    coordinationWithin :
      Geometry.coordinationMismatch mismatch ≤ coordinationTolerance tolerance

    solvationWithin :
      Geometry.solvationMismatch mismatch ≤ solvationTolerance tolerance

    conformationWithin :
      Geometry.conformationMismatch mismatch ≤ conformationTolerance tolerance

    kineticWithin :
      Geometry.kineticMismatch mismatch ≤ kineticTolerance tolerance

open WithinTolerance public

record TargetAdmissibleRegion : Set where
  constructor targetAdmissibleRegion
  field
    geometry : Geometry.TargetRecognitionGeometry
    tolerance : RecognitionTolerance

    hardGateCoordinatesPresent : Bool
    hardGateCoordinatesPresentIsTrue :
      hardGateCoordinatesPresent ≡ true

open TargetAdmissibleRegion public

AdmittedByRegion :
  TargetAdmissibleRegion →
  Geometry.RecognitionMismatch →
  Set
AdmittedByRegion region mismatch =
  WithinTolerance (tolerance region) mismatch

------------------------------------------------------------------------
-- Same pair, different coordinate-wise regions.
------------------------------------------------------------------------

permissiveTolerance : RecognitionTolerance
permissiveTolerance =
  recognitionTolerance
    0 0 0 0 2 0 0 0

strictCoordinationTolerance : RecognitionTolerance
strictCoordinationTolerance =
  recognitionTolerance
    0 0 0 0 1 0 0 0

permissiveRegion : TargetAdmissibleRegion
permissiveRegion =
  targetAdmissibleRegion
    Geometry.targetA
    permissiveTolerance
    true refl

strictCoordinationRegion : TargetAdmissibleRegion
strictCoordinationRegion =
  targetAdmissibleRegion
    Geometry.targetA
    strictCoordinationTolerance
    true refl

zeroLeqZero : 0 ≤ 0
zeroLeqZero = z≤n

oneLeqTwo : 1 ≤ 2
oneLeqTwo = s≤s z≤n

twoLeqTwo : 2 ≤ 2
twoLeqTwo = s≤s (s≤s z≤n)

canonicalPairInsidePermissiveRegion :
  AdmittedByRegion permissiveRegion Geometry.canonicalPairMismatch
canonicalPairInsidePermissiveRegion =
  withinTolerance
    zeroLeqZero
    zeroLeqZero
    zeroLeqZero
    zeroLeqZero
    twoLeqTwo
    zeroLeqZero
    zeroLeqZero
    zeroLeqZero

twoNotLeqOne : 2 ≤ 1 → ⊥
twoNotLeqOne ()

canonicalPairOutsideStrictCoordinationRegion :
  AdmittedByRegion strictCoordinationRegion Geometry.canonicalPairMismatch
  →
  ⊥
canonicalPairOutsideStrictCoordinationRegion admitted =
  twoNotLeqOne (coordinationWithin admitted)

record SamePairDifferentRegionWitness : Set where
  constructor samePairDifferentRegionWitness
  field
    pair : Geometry.RecognitionMismatch
    permissive : TargetAdmissibleRegion
    strict : TargetAdmissibleRegion

    admittedByPermissive :
      AdmittedByRegion permissive pair

    rejectedByStrict :
      AdmittedByRegion strict pair → ⊥

open SamePairDifferentRegionWitness public

canonicalSamePairDifferentRegionWitness :
  SamePairDifferentRegionWitness
canonicalSamePairDifferentRegionWitness =
  samePairDifferentRegionWitness
    Geometry.canonicalPairMismatch
    permissiveRegion
    strictCoordinationRegion
    canonicalPairInsidePermissiveRegion
    canonicalPairOutsideStrictCoordinationRegion

------------------------------------------------------------------------
-- Weighted score and hard gate are different semantics.
--
-- The canonical target A gives coordination weight zero, so the mismatch
-- scores zero and passes its scalar threshold.  The strict region still
-- rejects because coordination mismatch 2 exceeds tolerance 1.
------------------------------------------------------------------------

scalarScoreAcceptsCanonicalPair :
  Geometry.AdmissibleFor Geometry.targetA Geometry.canonicalPairMismatch
scalarScoreAcceptsCanonicalPair =
  Geometry.targetAAcceptsPair

hardRegionRejectsCanonicalPair :
  AdmittedByRegion
    strictCoordinationRegion
    Geometry.canonicalPairMismatch
  →
  ⊥
hardRegionRejectsCanonicalPair =
  canonicalPairOutsideStrictCoordinationRegion

data ScalarAcceptanceImpliesHardGateAcceptance : Set where

scalarAcceptanceDoesNotImplyHardGateAcceptance :
  ScalarAcceptanceImpliesHardGateAcceptance → ⊥
scalarAcceptanceDoesNotImplyHardGateAcceptance ()

------------------------------------------------------------------------
-- Mixed recognition policy.
------------------------------------------------------------------------

data RecognitionDecision : Set where
  acceptedByScoreAndRegion : RecognitionDecision
  scorePassRegionFail : RecognitionDecision
  scoreFailRegionPass : RecognitionDecision
  rejectedByBoth : RecognitionDecision

record MixedRecognitionPolicy : Set where
  constructor mixedRecognitionPolicy
  field
    targetGeometry : Geometry.TargetRecognitionGeometry
    admissibleRegion : TargetAdmissibleRegion

    scoreRequired : Bool
    regionRequired : Bool

    scoreRequiredIsTrue : scoreRequired ≡ true
    regionRequiredIsTrue : regionRequired ≡ true

open MixedRecognitionPolicy public

canonicalMixedRecognitionPolicy : MixedRecognitionPolicy
canonicalMixedRecognitionPolicy =
  mixedRecognitionPolicy
    Geometry.targetA
    strictCoordinationRegion
    true
    true
    refl
    refl

canonicalMixedDecision : RecognitionDecision
canonicalMixedDecision =
  scorePassRegionFail

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RecognitionAdmissibleRegionBoundary : Set where
  constructor recognitionAdmissibleRegionBoundary
  field
    weightedScoreAndHardGateSeparated : Bool
    weightedScoreAndHardGateSeparatedIsTrue :
      weightedScoreAndHardGateSeparated ≡ true

    coordinateFailureCanBlockDespiteLowScore : Bool
    coordinateFailureCanBlockDespiteLowScoreIsTrue :
      coordinateFailureCanBlockDespiteLowScore ≡ true

    tolerancesAreUniversalChemistryConstants : Bool
    tolerancesAreUniversalChemistryConstantsIsFalse :
      tolerancesAreUniversalChemistryConstants ≡ false

    empiricalToleranceCalibrationRequired : Bool
    empiricalToleranceCalibrationRequiredIsTrue :
      empiricalToleranceCalibrationRequired ≡ true

open RecognitionAdmissibleRegionBoundary public

canonicalRecognitionAdmissibleRegionBoundary :
  RecognitionAdmissibleRegionBoundary
canonicalRecognitionAdmissibleRegionBoundary =
  recognitionAdmissibleRegionBoundary
    true refl
    true refl
    false refl
    true refl
