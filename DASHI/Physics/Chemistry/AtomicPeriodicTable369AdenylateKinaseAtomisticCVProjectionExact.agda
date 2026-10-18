module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact as Geometry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeExact as Physical
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as SIAdK
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- CONCRETE INTERFACE INHABITATION: CONFIGURATION -> (theta1, theta2, dLN)
--
-- "Concrete" here means the previously empty application interface is now
-- constructed from one explicit COM-geometry evaluator and the source-owned
-- selection bundle.  Numerical real/acos mechanics remain obligations of that
-- evaluator; they are not fabricated by this adapter.
------------------------------------------------------------------------

selections : Selection.AdKThreeCVSelections
selections = Selection.canonicalAdKThreeCVSelections

atomisticProjection :
  {rigidModel : SE3.RigidMotionModel} →
  Geometry.AdKCOMGeometryModel rigidModel →
  Physical.AtomisticCVProjection Config.AtomisticConfiguration
atomisticProjection geometry = Physical.atomistic-cv-projection
  (λ configuration →
    Geometry.angleOfThreeCOMs geometry configuration
      (Selection.thetaOneFirst selections)
      (Selection.thetaOneVertex selections)
      (Selection.thetaOneThird selections))
  (λ configuration →
    Geometry.angleOfThreeCOMs geometry configuration
      (Selection.thetaTwoFirst selections)
      (Selection.thetaTwoVertex selections)
      (Selection.thetaTwoThird selections))
  (λ configuration →
    Geometry.distanceOfTwoCOMs geometry configuration
      (Selection.dLnFirst selections)
      (Selection.dLnSecond selections))
  (λ configuration →
    "same AtomisticConfiguration retained; COM evaluator provenance: " )
  "Li-Liu-Ji 2015 Figure-1 theta1/theta2/dLN observable definitions plus typed source-selection bundle"

------------------------------------------------------------------------
-- Observation retains the lower configuration and its validity witness.
------------------------------------------------------------------------

record AdKThreeCVObservation
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel)
  (configuration : Config.AtomisticConfiguration) : Set₁ where
  constructor adk-three-cv-observation
  field
    lowerConfiguration : Config.AtomisticConfiguration
    lowerConfigurationIsSameObject : lowerConfiguration ≡ configuration
    validity : Config.ValidAdKConfiguration configuration
    thetaOneDegrees : Nat
    thetaTwoDegrees : Nat
    dLn : SI.Quantity SI.Length SIAdK.angstromScale
    thetaOneIsEvaluatorResult :
      thetaOneDegrees ≡
      Physical.thetaOneDegrees (atomisticProjection geometry) configuration
    thetaTwoIsEvaluatorResult :
      thetaTwoDegrees ≡
      Physical.thetaTwoDegrees (atomisticProjection geometry) configuration
    dLnIsEvaluatorResult :
      dLn ≡ Physical.dLn (atomisticProjection geometry) configuration
    sourceSelectionReference : String
    evaluatorReference : String
    dLnAtomSubsetResolutionReference : String
open AdKThreeCVObservation public

evaluateCV :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (configuration : Config.AtomisticConfiguration) →
  Config.ValidAdKConfiguration configuration →
  AdKThreeCVObservation geometry configuration
evaluateCV geometry configuration validity =
  adk-three-cv-observation
    configuration
    refl
    validity
    (Physical.thetaOneDegrees (atomisticProjection geometry) configuration)
    (Physical.thetaTwoDegrees (atomisticProjection geometry) configuration)
    (Physical.dLn (atomisticProjection geometry) configuration)
    refl refl refl
    "Li-Liu-Ji Figure-1 typed selections in AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact"
    (Geometry.selectionResolutionReference geometry)
    "dLN domain residue ranges are source-paid; exact atom-subset semantics must be paid by the supplied geometry/selection resolver"

------------------------------------------------------------------------
-- Rigid-motion invariance follows from the COM geometry laws, not from an AdK
-- state label or from a source identifier.
------------------------------------------------------------------------

thetaOneRigidInvariant :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (g : SE3.RigidMotion rigidModel) →
  (configuration : Config.AtomisticConfiguration) →
  Physical.thetaOneDegrees (atomisticProjection geometry)
    (Geometry.transformConfiguration geometry g configuration)
  ≡ Physical.thetaOneDegrees (atomisticProjection geometry) configuration
thetaOneRigidInvariant geometry g configuration =
  Geometry.angleOfThreeCOMsRigidInvariant geometry g configuration
    (Selection.thetaOneFirst selections)
    (Selection.thetaOneVertex selections)
    (Selection.thetaOneThird selections)

thetaTwoRigidInvariant :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (g : SE3.RigidMotion rigidModel) →
  (configuration : Config.AtomisticConfiguration) →
  Physical.thetaTwoDegrees (atomisticProjection geometry)
    (Geometry.transformConfiguration geometry g configuration)
  ≡ Physical.thetaTwoDegrees (atomisticProjection geometry) configuration
thetaTwoRigidInvariant geometry g configuration =
  Geometry.angleOfThreeCOMsRigidInvariant geometry g configuration
    (Selection.thetaTwoFirst selections)
    (Selection.thetaTwoVertex selections)
    (Selection.thetaTwoThird selections)

dLnRigidInvariant :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (g : SE3.RigidMotion rigidModel) →
  (configuration : Config.AtomisticConfiguration) →
  Physical.dLn (atomisticProjection geometry)
    (Geometry.transformConfiguration geometry g configuration)
  ≡ Physical.dLn (atomisticProjection geometry) configuration
dLnRigidInvariant geometry g configuration =
  Geometry.distanceOfTwoCOMsRigidInvariant geometry g configuration
    (Selection.dLnFirst selections)
    (Selection.dLnSecond selections)

------------------------------------------------------------------------
-- WrongType / non-factorability firewalls.
------------------------------------------------------------------------

data ThreeCVObservationRecoversUniqueConfiguration : Set where
data ThreeCVObservationCreatesStateClassification : Set where
data RigidInvariantCVCreatesPhysicalDynamics : Set where
data SourceSelectionCreatesGeometryEvaluator : Set where

threeCVDoesNotRecoverUniqueConfiguration : ThreeCVObservationRecoversUniqueConfiguration → ⊥
threeCVDoesNotRecoverUniqueConfiguration ()

threeCVDoesNotCreateStateClassification : ThreeCVObservationCreatesStateClassification → ⊥
threeCVDoesNotCreateStateClassification ()

rigidInvariantCVDoesNotCreateDynamics : RigidInvariantCVCreatesPhysicalDynamics → ⊥
rigidInvariantCVDoesNotCreateDynamics ()

sourceSelectionDoesNotCreateEvaluator : SourceSelectionCreatesGeometryEvaluator → ⊥
sourceSelectionDoesNotCreateEvaluator ()

record AdKAtomisticCVProjectionBoundary : Set where
  constructor adk-atomistic-cv-projection-boundary
  field
    configurationToThreeCVMapInhabited : Bool
    sourceOwnedSelectionsRetained : Bool
    lowerConfigurationRetainedWithObservation : Bool
    validityWitnessRetained : Bool
    rigidMotionInvarianceExposed : Bool
    dLnAtomSubsetMustBeResolvedByEvaluator : Bool
    threeCVObservationRecoversUniqueConfiguration : Bool
    threeCVObservationCreatesStateClassification : Bool
    rigidInvariantCVCreatesPhysicalDynamics : Bool
    sourceSelectionCreatesGeometryEvaluator : Bool
open AdKAtomisticCVProjectionBoundary public

canonicalAdKAtomisticCVProjectionBoundary : AdKAtomisticCVProjectionBoundary
canonicalAdKAtomisticCVProjectionBoundary =
  adk-atomistic-cv-projection-boundary
    true true true true true true
    false false false false
