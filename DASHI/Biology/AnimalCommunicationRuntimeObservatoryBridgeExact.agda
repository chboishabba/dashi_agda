module DASHI.Biology.AnimalCommunicationRuntimeObservatoryBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalCommunicationPassiveAcousticLocalizationExact as Acoustic
import DASHI.Biology.AnimalCommunicationMultiObserverVisualBridgeExact as Visual
import DASHI.Biology.AnimalCommunicationSharedWorldAVAssociationExact as AV

------------------------------------------------------------------------
-- ANIMALEXIC PYTHON RUNTIME HANDOFF
--
-- This owner pins the executable producer surface that corresponds to the
-- formal passive-localization / multi-observer / shared-world AV architecture.
-- Runtime source presence is not identified with pytest, field validation,
-- species identity, same-object identity, or semantic authority.
------------------------------------------------------------------------

record AnimalCommunicationRuntimeObservatoryReceipt : Set where
  constructor animal-communication-runtime-observatory-receipt
  field
    repositoryReference : String
    parentGeometryBranchReference : String
    runtimeBranchReference : String
    runtimeHeadReference : String
    receiptSchema : String
    passiveLocalizationScript : String
    sharedWorldAssociationScript : String
    runtimeTestReference : String
    passiveLocalizationOwnerReference : String
    visualBridgeOwnerReference : String
    sharedWorldAVOwnerReference : String
    pythonRuntimeCandidateWritten : Bool
    runtimePytestReceiptObserved : Bool
    agdaKernelReceiptObserved : Bool
    realSynchronizedMicrophoneValidationObserved : Bool
    realTrailCameraWorldTrackValidationObserved : Bool
    fieldValidationObserved : Bool
    activeAcousticProbeRequired : Bool
    runtimePromotionAuthorityClaimed : Bool

open AnimalCommunicationRuntimeObservatoryReceipt public

currentAnimalCommunicationRuntimeObservatoryReceipt :
  AnimalCommunicationRuntimeObservatoryReceipt
currentAnimalCommunicationRuntimeObservatoryReceipt =
  animal-communication-runtime-observatory-receipt
    "chboishabba/animalexic"
    "agent/issue20-known-pose-multiview @ af5e020d72e01b22d3602519ba27e5d9797634c7"
    "agent/animal-communication-observatory-runtime"
    "59c9a89fefb19ca84facfd2aa02ac3037ba08a12"
    "animalexic-animal-communication-observatory-v1"
    "scripts/passive_acoustic_localization.py"
    "scripts/animal_communication_observatory.py"
    "tests/test_animal_communication_observatory.py"
    "DASHI.Biology.AnimalCommunicationPassiveAcousticLocalizationExact"
    "DASHI.Biology.AnimalCommunicationMultiObserverVisualBridgeExact"
    "DASHI.Biology.AnimalCommunicationSharedWorldAVAssociationExact"
    true
    false
    false
    false
    false
    false
    false
    false

record RuntimeObservatoryBoundary : Set where
  constructor runtime-observatory-boundary
  field
    pythonSourceDoesNotCreatePytestReceipt : Bool
    pytestReceiptDoesNotCreateFieldValidation : Bool
    tdoaLocalizationDoesNotCreateSpeciesIdentity : Bool
    visualTrackDoesNotCreateIndividualIdentity : Bool
    avAssociationDoesNotCreateSameObjectIdentity : Bool
    sameObjectIdentityDoesNotCreateSemanticMeaning : Bool
    passiveObservationDoesNotCreateInterventionAuthority : Bool
    runtimeReceiptPreservesCandidateStatus : Bool

open RuntimeObservatoryBoundary public

canonicalRuntimeObservatoryBoundary : RuntimeObservatoryBoundary
canonicalRuntimeObservatoryBoundary =
  runtime-observatory-boundary true true true true true true true true

runtimeReading : String
runtimeReading =
  "Animalexic now has a candidate-only Python handoff for passive synchronized-microphone localization and shared-world trail-camera/audio association. The runtime may narrow a many-to-many emitter relation and emit append-only observatory receipts, but source presence alone is not pytest success, field validation, same-object identity, species/individual identity, semantic meaning, or intervention authority."
