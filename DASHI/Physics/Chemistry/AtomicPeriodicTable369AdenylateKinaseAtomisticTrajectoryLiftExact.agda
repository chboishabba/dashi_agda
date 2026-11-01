module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticTrajectoryLiftExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as SIAdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact as Geometry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionExact as Projection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeExact as Physical
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph

------------------------------------------------------------------------
-- ATOMISTIC TRAJECTORY -> CV TRAJECTORY -> STATE PATH
--
-- Every projected frame retains the lower frame.  The maps are one-way
-- abstraction maps; neither CV observations nor state labels reconstruct the
-- unique atomistic trajectory, and a state path does not manufacture kinetics.
------------------------------------------------------------------------

record AtomisticTrajectoryFrame : Set where
  constructor atomistic-trajectory-frame
  field
    time : SI.Quantity SI.Time SI.nanoScale
    configuration : Config.AtomisticConfiguration
    frameManifestReference : String
open AtomisticTrajectoryFrame public

record AtomisticTrajectory : Set where
  constructor atomistic-trajectory
  field
    frames : List AtomisticTrajectoryFrame
    trajectoryManifestReference : String
    sourceOrExecutionReference : String
open AtomisticTrajectory public

record CVTrajectoryFrame
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) : Set₁ where
  constructor cv-trajectory-frame
  field
    lowerFrame : AtomisticTrajectoryFrame
    lowerConfigurationValidity :
      Config.ValidAdKConfiguration (configuration lowerFrame)
    observation :
      Projection.AdKThreeCVObservation geometry (configuration lowerFrame)
    observationIsProjectionOfLowerFrame :
      observation ≡ Projection.evaluateCV geometry
        (configuration lowerFrame)
        lowerConfigurationValidity
open CVTrajectoryFrame public

record StatePathFrame
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel)
  (classifier :
    Physical.CVStateClassifier
      Config.AtomisticConfiguration
      (Projection.atomisticProjection geometry)) : Set₁ where
  constructor state-path-frame
  field
    lowerCVFrame : CVTrajectoryFrame geometry
    state : Graph.AdKLandscapeState
    stateIsClassifierOutput :
      state ≡ Physical.classify classifier
        (configuration (lowerFrame lowerCVFrame))
open StatePathFrame public

record TrajectoryLiftContext
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) : Set₁ where
  constructor trajectory-lift-context
  field
    validityFor :
      (frame : AtomisticTrajectoryFrame) →
      Config.ValidAdKConfiguration (configuration frame)
    classifier :
      Physical.CVStateClassifier
        Config.AtomisticConfiguration
        (Projection.atomisticProjection geometry)
    validityProvenance : String
    classifierProvenance : String
open TrajectoryLiftContext public

liftAtomisticFrame :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (context : TrajectoryLiftContext geometry) →
  (frame : AtomisticTrajectoryFrame) →
  CVTrajectoryFrame geometry
liftAtomisticFrame geometry context frame =
  cv-trajectory-frame
    frame
    (validityFor context frame)
    (Projection.evaluateCV geometry
      (configuration frame)
      (validityFor context frame))
    refl

classifyCVFrame :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (context : TrajectoryLiftContext geometry) →
  CVTrajectoryFrame geometry →
  StatePathFrame geometry (classifier context)
classifyCVFrame geometry context frame =
  state-path-frame
    frame
    (Physical.classify (classifier context)
      (configuration (lowerFrame frame)))
    refl

liftAtomisticFrames :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (context : TrajectoryLiftContext geometry) →
  List AtomisticTrajectoryFrame →
  List (CVTrajectoryFrame geometry)
liftAtomisticFrames geometry context [] = []
liftAtomisticFrames geometry context (frame ∷ rest) =
  liftAtomisticFrame geometry context frame ∷
  liftAtomisticFrames geometry context rest

classifyCVFrames :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (context : TrajectoryLiftContext geometry) →
  List (CVTrajectoryFrame geometry) →
  List (StatePathFrame geometry (classifier context))
classifyCVFrames geometry context [] = []
classifyCVFrames geometry context (frame ∷ rest) =
  classifyCVFrame geometry context frame ∷
  classifyCVFrames geometry context rest

record LiftedAdKTrajectory
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel)
  (context : TrajectoryLiftContext geometry) : Set₁ where
  constructor lifted-adk-trajectory
  field
    atomistic : AtomisticTrajectory
    cvFrames : List (CVTrajectoryFrame geometry)
    stateFrames : List (StatePathFrame geometry (classifier context))
    cvFramesAreProjection :
      cvFrames ≡ liftAtomisticFrames geometry context (frames atomistic)
    stateFramesAreClassification :
      stateFrames ≡ classifyCVFrames geometry context cvFrames
    lowerCarrierRetentionReference : String
open LiftedAdKTrajectory public

liftTrajectory :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  (context : TrajectoryLiftContext geometry) →
  AtomisticTrajectory →
  LiftedAdKTrajectory geometry context
liftTrajectory geometry context trajectory =
  lifted-adk-trajectory
    trajectory
    projected
    (classifyCVFrames geometry context projected)
    refl
    refl
    "every CV frame retains its AtomisticTrajectoryFrame; every state frame retains its CV frame; projection/classification never erase provenance by construction"
  where
    projected : List (CVTrajectoryFrame geometry)
    projected = liftAtomisticFrames geometry context (frames trajectory)

------------------------------------------------------------------------
-- WrongType / information-loss firewalls.
------------------------------------------------------------------------

data CVTrajectoryDeterminesUniqueAtomisticTrajectory : Set where
data StatePathDeterminesUniqueCVTrajectory : Set where
data StatePathCreatesPhysicalKinetics : Set where
data StateTransitionCreatesAtomisticMechanism : Set where
data TrajectorySourceLabelCreatesFrameCoordinates : Set where

cvTrajectoryDoesNotDetermineUniqueAtomistic : CVTrajectoryDeterminesUniqueAtomisticTrajectory → ⊥
cvTrajectoryDoesNotDetermineUniqueAtomistic ()

statePathDoesNotDetermineUniqueCVTrajectory : StatePathDeterminesUniqueCVTrajectory → ⊥
statePathDoesNotDetermineUniqueCVTrajectory ()

statePathDoesNotCreatePhysicalKinetics : StatePathCreatesPhysicalKinetics → ⊥
statePathDoesNotCreatePhysicalKinetics ()

stateTransitionDoesNotCreateAtomisticMechanism : StateTransitionCreatesAtomisticMechanism → ⊥
stateTransitionDoesNotCreateAtomisticMechanism ()

trajectorySourceLabelDoesNotCreateCoordinates : TrajectorySourceLabelCreatesFrameCoordinates → ⊥
trajectorySourceLabelDoesNotCreateCoordinates ()

record AdKAtomisticTrajectoryLiftBoundary : Set where
  constructor adk-atomistic-trajectory-lift-boundary
  field
    timeIndexedAtomisticFramesRetained : Bool
    atomisticTrajectoryToCVTrajectoryDefined : Bool
    cvTrajectoryToStatePathDefined : Bool
    validityWitnessRetainedPerFrame : Bool
    lowerFrameRetainedAtEveryProjection : Bool
    classifierProvenanceExplicit : Bool
    cvTrajectoryDeterminesUniqueAtomisticTrajectory : Bool
    statePathDeterminesUniqueCVTrajectory : Bool
    statePathCreatesPhysicalKinetics : Bool
    stateTransitionCreatesAtomisticMechanism : Bool
    sourceLabelCreatesFrameCoordinates : Bool
open AdKAtomisticTrajectoryLiftBoundary public

canonicalAdKAtomisticTrajectoryLiftBoundary : AdKAtomisticTrajectoryLiftBoundary
canonicalAdKAtomisticTrajectoryLiftBoundary =
  adk-atomistic-trajectory-lift-boundary
    true true true true true true
    false false false false false
