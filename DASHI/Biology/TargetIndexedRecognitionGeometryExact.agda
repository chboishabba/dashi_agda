module DASHI.Biology.TargetIndexedRecognitionGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Biology.TargetRelativeRecognitionFibreExact as Fibre
import DASHI.Biology.IonicMimicryGeometryExact as Ionic
import DASHI.Biology.BioactiveMolecularRecognitionBridge as Recognition

------------------------------------------------------------------------
-- TARGET-INDEXED ANISOTROPIC RECOGNITION GEOMETRY
--
-- A pair of chemical species does not carry one universal biological
-- similarity distance.  A target chooses which mismatch coordinates matter
-- and how strongly they matter.
--
-- This finite Nat-valued carrier is intentionally an exact structural model,
-- not a calibrated binding-energy metric.
------------------------------------------------------------------------

record RecognitionMismatch : Set where
  constructor recognitionMismatch
  field
    chargeMismatch : Nat
    sizeShapeMismatch : Nat
    donorAcceptorMismatch : Nat
    localGeometryMismatch : Nat
    coordinationMismatch : Nat
    solvationMismatch : Nat
    conformationMismatch : Nat
    kineticMismatch : Nat

open RecognitionMismatch public

zeroRecognitionMismatch : RecognitionMismatch
zeroRecognitionMismatch =
  recognitionMismatch 0 0 0 0 0 0 0 0

record TargetRecognitionWeights : Set where
  constructor targetRecognitionWeights
  field
    chargeWeight : Nat
    sizeShapeWeight : Nat
    donorAcceptorWeight : Nat
    localGeometryWeight : Nat
    coordinationWeight : Nat
    solvationWeight : Nat
    conformationWeight : Nat
    kineticWeight : Nat

open TargetRecognitionWeights public

weightedMismatch :
  TargetRecognitionWeights →
  RecognitionMismatch →
  Nat
weightedMismatch weights mismatch =
  chargeWeight weights * chargeMismatch mismatch +
  sizeShapeWeight weights * sizeShapeMismatch mismatch +
  donorAcceptorWeight weights * donorAcceptorMismatch mismatch +
  localGeometryWeight weights * localGeometryMismatch mismatch +
  coordinationWeight weights * coordinationMismatch mismatch +
  solvationWeight weights * solvationMismatch mismatch +
  conformationWeight weights * conformationMismatch mismatch +
  kineticWeight weights * kineticMismatch mismatch

record TargetRecognitionGeometry : Set where
  constructor targetRecognitionGeometry
  field
    targetReference : String
    weights : TargetRecognitionWeights
    threshold : Nat
    protocolReference : String

    weightsAreModelCoordinates : Bool
    weightsAreModelCoordinatesIsTrue :
      weightsAreModelCoordinates ≡ true

    weightsAreEmpiricallyCalibrated : Bool
    weightsAreEmpiricallyCalibratedIsFalse :
      weightsAreEmpiricallyCalibrated ≡ false

open TargetRecognitionGeometry public

AdmissibleFor :
  TargetRecognitionGeometry →
  RecognitionMismatch →
  Set
AdmissibleFor target mismatch =
  weightedMismatch (weights target) mismatch ≤ threshold target

------------------------------------------------------------------------
-- Same pair, different target.
--
-- The fixture is deliberately tiny:
--
--   pair mismatch = no charge mismatch + coordination mismatch 2
--
-- Target A ignores coordination mismatch and accepts the pair.
-- Target B strongly weights coordination mismatch and rejects the pair.
--
-- This proves target relativity without claiming these are measured weights
-- for any real protein.
------------------------------------------------------------------------

canonicalPairMismatch : RecognitionMismatch
canonicalPairMismatch =
  recognitionMismatch
    0   -- charge
    0   -- size / shape
    0   -- donor / acceptor
    0   -- local geometry
    2   -- coordination geometry
    0   -- solvation
    0   -- conformation
    0   -- kinetics

chargeDominantWeights : TargetRecognitionWeights
chargeDominantWeights =
  targetRecognitionWeights
    3 0 0 0 0 0 0 0

coordinationSensitiveWeights : TargetRecognitionWeights
coordinationSensitiveWeights =
  targetRecognitionWeights
    0 0 0 0 3 0 0 0

targetA : TargetRecognitionGeometry
targetA =
  targetRecognitionGeometry
    "finite fixture target A: charge-sensitive / coordination-insensitive"
    chargeDominantWeights
    1
    "DASHI structural fixture only"
    true refl
    false refl

targetB : TargetRecognitionGeometry
targetB =
  targetRecognitionGeometry
    "finite fixture target B: coordination-sensitive"
    coordinationSensitiveWeights
    2
    "DASHI structural fixture only"
    true refl
    false refl

targetAScoreIsZero :
  weightedMismatch (weights targetA) canonicalPairMismatch ≡ 0
targetAScoreIsZero = refl

targetBScoreIsSix :
  weightedMismatch (weights targetB) canonicalPairMismatch ≡ 6
targetBScoreIsSix = refl

targetAAcceptsPair :
  AdmissibleFor targetA canonicalPairMismatch
targetAAcceptsPair =
  z≤n

sixNotLeqTwo : 6 ≤ 2 → ⊥
sixNotLeqTwo ()

targetBRejectsPair :
  AdmissibleFor targetB canonicalPairMismatch → ⊥
targetBRejectsPair =
  sixNotLeqTwo

record SamePairDifferentTargetWitness : Set where
  constructor samePairDifferentTargetWitness
  field
    pair : RecognitionMismatch
    acceptingTarget : TargetRecognitionGeometry
    rejectingTarget : TargetRecognitionGeometry

    accepted :
      AdmissibleFor acceptingTarget pair

    rejected :
      AdmissibleFor rejectingTarget pair → ⊥

    pairUnchangedAcrossTargets : Bool
    pairUnchangedAcrossTargetsIsTrue :
      pairUnchangedAcrossTargets ≡ true

open SamePairDifferentTargetWitness public

canonicalSamePairDifferentTargetWitness :
  SamePairDifferentTargetWitness
canonicalSamePairDifferentTargetWitness =
  samePairDifferentTargetWitness
    canonicalPairMismatch
    targetA
    targetB
    targetAAcceptsPair
    targetBRejectsPair
    true refl

------------------------------------------------------------------------
-- Recognition geometry is anisotropic.
------------------------------------------------------------------------

isotropicUnitWeights : TargetRecognitionWeights
isotropicUnitWeights =
  targetRecognitionWeights 1 1 1 1 1 1 1 1

anisotropicExampleWeights : TargetRecognitionWeights
anisotropicExampleWeights =
  targetRecognitionWeights 1 0 3 5 2 0 4 1

record AnisotropicRecognitionWitness : Set where
  constructor anisotropicRecognitionWitness
  field
    isotropic : TargetRecognitionWeights
    anisotropic : TargetRecognitionWeights

    chargeWeightDiffersFromGeometryWeight :
      chargeWeight anisotropic
      ≡
      localGeometryWeight anisotropic
      →
      ⊥

    zeroWeightCoordinateExists : Bool
    zeroWeightCoordinateExistsIsTrue :
      zeroWeightCoordinateExists ≡ true

open AnisotropicRecognitionWitness public

oneNotFive : 1 ≡ 5 → ⊥
oneNotFive ()

canonicalAnisotropicRecognitionWitness :
  AnisotropicRecognitionWitness
canonicalAnisotropicRecognitionWitness =
  anisotropicRecognitionWitness
    isotropicUnitWeights
    anisotropicExampleWeights
    oneNotFive
    true refl

------------------------------------------------------------------------
-- Biological instances are consumers, not definitionally equal to the
-- fixture metric.
------------------------------------------------------------------------

ionicRecognitionFibre : Fibre.TargetRelativeRecognitionFibre
ionicRecognitionFibre =
  Fibre.canonicalPbCaRecognitionFibre

serotoninLSDRecognitionFibre : Fibre.TargetRelativeRecognitionFibre
serotoninLSDRecognitionFibre =
  Fibre.canonicalSerotoninLSDRecognitionFibre

ionicMimicryBoundary : Ionic.IonicMimicryGeometryBoundary
ionicMimicryBoundary =
  Ionic.canonicalIonicMimicryGeometryBoundary

recognitionSimilarityCarriers :
  List Recognition.BioactiveSimilarityCarrier
recognitionSimilarityCarriers =
  Recognition.canonicalBioactiveSimilarityCarriers

------------------------------------------------------------------------
-- Calibration contract for a real target.
------------------------------------------------------------------------

record RecognitionGeometryCalibration : Set where
  constructor recognitionGeometryCalibration
  field
    target : TargetRecognitionGeometry
    sourceReference : String
    assayReference : String

    chargeCalibration : String
    geometryCalibration : String
    solvationCalibration : String
    conformationCalibration : String
    kineticsCalibration : String
    thresholdCalibration : String

    sameAssayCoordinateSystem : Bool
    sameAssayCoordinateSystemIsTrue :
      sameAssayCoordinateSystem ≡ true

    calibrationAccepted : Bool
    calibrationAcceptedIsFalse :
      calibrationAccepted ≡ false

open RecognitionGeometryCalibration public

canonicalUncalibratedRecognitionGeometry :
  RecognitionGeometryCalibration
canonicalUncalibratedRecognitionGeometry =
  recognitionGeometryCalibration
    targetB
    "no empirical weight source attached"
    "finite theorem fixture"
    "open"
    "open"
    "open"
    "open"
    "open"
    "open"
    true refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data OneUniversalRecognitionMetric : Set where
data LowMismatchMeansSameChemicalIdentity : Set where
data LowMismatchMeansSameFunctionalOutcome : Set where
data WeightZeroMeansCoordinateBiologicallyIrrelevant : Set where
data ArbitraryWeightsAreEmpiricalAffinity : Set where

universalMetricBlocked :
  OneUniversalRecognitionMetric → ⊥
universalMetricBlocked ()

lowMismatchDoesNotMeanIdentity :
  LowMismatchMeansSameChemicalIdentity → ⊥
lowMismatchDoesNotMeanIdentity ()

lowMismatchDoesNotMeanSameOutcome :
  LowMismatchMeansSameFunctionalOutcome → ⊥
lowMismatchDoesNotMeanSameOutcome ()

zeroModelWeightDoesNotProveBiologicalIrrelevance :
  WeightZeroMeansCoordinateBiologicallyIrrelevant → ⊥
zeroModelWeightDoesNotProveBiologicalIrrelevance ()

arbitraryWeightsDoNotBecomeAffinity :
  ArbitraryWeightsAreEmpiricalAffinity → ⊥
arbitraryWeightsDoNotBecomeAffinity ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record TargetIndexedRecognitionGeometryBoundary : Set where
  constructor targetIndexedRecognitionGeometryBoundary
  field
    samePairCanDifferAcrossTargets : Bool
    samePairCanDifferAcrossTargetsIsTrue :
      samePairCanDifferAcrossTargets ≡ true

    recognitionGeometryCanBeAnisotropic : Bool
    recognitionGeometryCanBeAnisotropicIsTrue :
      recognitionGeometryCanBeAnisotropic ≡ true

    targetMetricIsUniversalMolecularMetric : Bool
    targetMetricIsUniversalMolecularMetricIsFalse :
      targetMetricIsUniversalMolecularMetric ≡ false

    finiteWeightsAreBindingFreeEnergies : Bool
    finiteWeightsAreBindingFreeEnergiesIsFalse :
      finiteWeightsAreBindingFreeEnergies ≡ false

    empiricalCalibrationStillRequired : Bool
    empiricalCalibrationStillRequiredIsTrue :
      empiricalCalibrationStillRequired ≡ true

open TargetIndexedRecognitionGeometryBoundary public

canonicalTargetIndexedRecognitionGeometryBoundary :
  TargetIndexedRecognitionGeometryBoundary
canonicalTargetIndexedRecognitionGeometryBoundary =
  targetIndexedRecognitionGeometryBoundary
    true refl
    true refl
    false refl
    false refl
    true refl
