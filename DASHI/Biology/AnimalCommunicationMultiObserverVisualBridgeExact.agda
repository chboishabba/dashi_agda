module DASHI.Biology.AnimalCommunicationMultiObserverVisualBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicIssue20KnownPoseMultiViewExact as KnownPose
import DASHI.Biology.AnimalexicHandheldMultiCameraPoseFibreExact as Pose
import DASHI.Biology.AnimalexicCrossCameraWorldWeldExact as Weld
import DASHI.Biology.AnimalCommunicationSceneObservationExact as Scene

------------------------------------------------------------------------
-- MULTI-OBSERVER VISUAL -> ANIMAL COMMUNICATION BRIDGE
--
-- Reuses Animalexic camera pose / world-weld candidate geometry as a visual
-- observer for animal communication scenes.  It does not create a second
-- vision ontology and does not promote geometry into biological identity.
------------------------------------------------------------------------

record MultiObserverAnimalTrackReceipt : Set where
  constructor multi-observer-animal-track-receipt
  field
    sourceSceneReference : String
    cameraObservationReferences : String
    cameraPoseFibreReference : String
    sharedWorldWeldReference : String
    dynamicTrackReference : String
    candidateWorldRegionReference : String
    morphologyEvidenceReference : String
    motionGaitEvidenceReference : String
    speciesHypothesisReference : String
    individualHypothesisReference : String
    provenanceReference : String
    dynamicTargetMaskedFromCameraPoseEstimation : Bool
    sharedWorldTrackPaid : Bool
    speciesIdentityPaid : Bool
    individualIdentityPaid : Bool
    outputIsCandidate : Bool

open MultiObserverAnimalTrackReceipt public

record VisualToCommunicationParticipantAdapter : Set where
  constructor visual-to-communication-participant-adapter
  field
    visualTrackReference : String
    participantReference : String
    sceneEmitterCandidateReference : String
    worldRegionReference : String
    crossCameraContinuityReference : String
    associationResidualReference : String
    provenanceReference : String
    preservesCandidateStatus : Bool
    createsVocalEmitterIdentity : Bool
    createsSemanticMeaning : Bool

open VisualToCommunicationParticipantAdapter public

------------------------------------------------------------------------
-- Firewalls inherited from the existing Animalexic geometry discipline.
------------------------------------------------------------------------

data DynamicTargetCreatesCameraPosePermission : Set where

data SameWorldTrackCreatesSpeciesIdentityPermission : Set where

data SpeciesIdentityCreatesIndividualIdentityPermission : Set where

data VisualTrackCreatesVocalEmitterIdentityPermission : Set where

data CrossCameraContinuityCreatesSemanticContinuityPermission : Set where

data LowWorldWeldResidualCreatesSameAnimalPermission : Set where

dynamicTargetDoesNotCreateCameraPose :
  DynamicTargetCreatesCameraPosePermission → ⊥
dynamicTargetDoesNotCreateCameraPose ()

sameWorldTrackDoesNotCreateSpeciesIdentity :
  SameWorldTrackCreatesSpeciesIdentityPermission → ⊥
sameWorldTrackDoesNotCreateSpeciesIdentity ()

speciesIdentityDoesNotCreateIndividualIdentity :
  SpeciesIdentityCreatesIndividualIdentityPermission → ⊥
speciesIdentityDoesNotCreateIndividualIdentity ()

visualTrackDoesNotCreateVocalEmitterIdentity :
  VisualTrackCreatesVocalEmitterIdentityPermission → ⊥
visualTrackDoesNotCreateVocalEmitterIdentity ()

crossCameraContinuityDoesNotCreateSemanticContinuity :
  CrossCameraContinuityCreatesSemanticContinuityPermission → ⊥
crossCameraContinuityDoesNotCreateSemanticContinuity ()

lowWorldWeldResidualDoesNotCreateSameAnimal :
  LowWorldWeldResidualCreatesSameAnimalPermission → ⊥
lowWorldWeldResidualDoesNotCreateSameAnimal ()

record MultiObserverVisualBridgeBoundary : Set where
  constructor multi-observer-visual-bridge-boundary
  field
    reusesKnownPoseMultiView : Bool
    reusesHandheldPoseFibre : Bool
    reusesCrossCameraWorldWeld : Bool
    dynamicTargetEvidenceSeparateFromCameraPose : Bool
    sharedWorldTrackIsCandidateOnly : Bool
    speciesAndIndividualIdentityRemainSeparate : Bool
    visualToAcousticEmitterAssociationNeedsReceipt : Bool
    trailCameraDeploymentCompatible : Bool

open MultiObserverVisualBridgeBoundary public

canonicalMultiObserverVisualBridgeBoundary : MultiObserverVisualBridgeBoundary
canonicalMultiObserverVisualBridgeBoundary =
  multi-observer-visual-bridge-boundary
    true true true true true true true true

knownPoseOwnerReused : String
knownPoseOwnerReused =
  "DASHI.Biology.AnimalexicIssue20KnownPoseMultiViewExact"

poseFibreOwnerReused : String
poseFibreOwnerReused =
  "DASHI.Biology.AnimalexicHandheldMultiCameraPoseFibreExact"

worldWeldOwnerReused : String
worldWeldOwnerReused =
  "DASHI.Biology.AnimalexicCrossCameraWorldWeldExact"

communicationSceneOwnerReused : String
communicationSceneOwnerReused =
  "DASHI.Biology.AnimalCommunicationSceneObservationExact"

visualBridgeReading : String
visualBridgeReading =
  "Trail-camera and multi-observer visual evidence enters the AnimalCommunication scene through existing candidate camera-pose and shared-world-weld fibres. Dynamic animals may define candidate body/world tracks while remaining masked from camera-pose estimation. Shared-world continuity can strengthen same-object hypotheses but does not create species, individual, vocal-emitter or semantic identity."
