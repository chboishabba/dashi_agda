module DASHI.Biology.AnimalCommunicationPassiveAcousticLocalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.AnimalCommunicationSceneObservationExact as Scene

------------------------------------------------------------------------
-- PASSIVE ACOUSTIC LOCALIZATION
--
-- This owner represents synchronized-microphone localization as a candidate
-- observer over an AnimalCommunication scene.  It does not implement a TDOA
-- solver or beamformer in Agda and does not use active acoustic probing.
------------------------------------------------------------------------

record PassiveAcousticLocalizationReceipt : Set where
  constructor passive-acoustic-localization-receipt
  field
    sceneReference : String
    signalEventReference : String
    microphoneArrayReference : String
    microphoneGeometryReference : String
    clockCalibrationReference : String
    timeDifferenceOfArrivalReference : String
    phaseDifferenceReference : String
    levelDifferenceReference : String
    beamformingOrSpatialFilterReference : String
    propagationMediumReference : String
    candidateWorldRegionReference : String
    localizationResidualReference : String
    sourceMixtureReference : String
    provenanceReference : String
    clockSynchronizationPaid : Bool
    microphoneGeometryPaid : Bool
    mediumModelPaid : Bool
    candidateLocalizationOnly : Bool
    uniqueEmitterPaid : Bool
    speciesIdentityPaid : Bool
    activeProbeUsed : Bool

open PassiveAcousticLocalizationReceipt public

------------------------------------------------------------------------
-- Same candidate acoustic region can be consistent with different birds.
-- Localization narrows the inverse fibre; it does not identify the emitter.
------------------------------------------------------------------------

data LocalizationWorld : Set where
  magpieInRegion : LocalizationWorld
  lorikeetInRegion : LocalizationWorld

data LocalizationSurface : Set where
  sameCandidateWorldRegion : LocalizationSurface

data LocalizationQuery : Set where
  emitterIdentityQuery : LocalizationQuery

data LocalizationAnswer : Set where
  magpieEmitter : LocalizationAnswer
  lorikeetEmitter : LocalizationAnswer

localizationProjection : LocalizationWorld → LocalizationSurface
localizationProjection world = sameCandidateWorldRegion

localizationAnswer : LocalizationQuery → LocalizationWorld → LocalizationAnswer
localizationAnswer emitterIdentityQuery magpieInRegion = magpieEmitter
localizationAnswer emitterIdentityQuery lorikeetInRegion = lorikeetEmitter

localizationSemantics :
  Query.QuerySemantics LocalizationWorld LocalizationQuery LocalizationAnswer
localizationSemantics = Query.querySemantics localizationAnswer

localizedCallEmitterDefect :
  Query.QueryAdequacyDefect
    localizationProjection localizationSemantics emitterIdentityQuery
localizedCallEmitterDefect =
  Query.queryAdequacyDefect
    magpieInRegion
    lorikeetInRegion
    refl
    (λ ())

localizedCallDoesNotCreateUniqueBird :
  Query.AdequateFor
    localizationProjection localizationSemantics emitterIdentityQuery → ⊥
localizedCallDoesNotCreateUniqueBird =
  Query.queryAdequacyDefectBlocksFactorisation localizedCallEmitterDefect

------------------------------------------------------------------------
-- Additional authority firewalls.
------------------------------------------------------------------------

data TDOAFitCreatesSpeciesIdentityPermission : Set where

data LocalizationCreatesInteractionPermission : Set where

data PassiveObservationCreatesInterventionAuthorityPermission : Set where

tdoaFitDoesNotCreateSpeciesIdentity :
  TDOAFitCreatesSpeciesIdentityPermission → ⊥
tdoaFitDoesNotCreateSpeciesIdentity ()

localizationDoesNotCreateInteraction :
  LocalizationCreatesInteractionPermission → ⊥
localizationDoesNotCreateInteraction ()

passiveObservationDoesNotCreateInterventionAuthority :
  PassiveObservationCreatesInterventionAuthorityPermission → ⊥
passiveObservationDoesNotCreateInterventionAuthority ()

record PassiveAcousticLocalizationBoundary : Set where
  constructor passive-acoustic-localization-boundary
  field
    synchronizedMicrophonesAreObserver : Bool
    tdoaIsCandidateLocalizationEvidence : Bool
    phaseAndLevelDifferencesMayRefine : Bool
    propagationMediumRemainsExplicit : Bool
    unresolvedMixturesRemainFirstClass : Bool
    localizationIsNotSpeciesIdentity : Bool
    localizationIsNotUniqueEmitterIdentity : Bool
    localizationIsNotSemanticMeaning : Bool
    passiveLaneSeparateFromPlaybackIntervention : Bool
    activeProbeUsedInCanonicalLane : Bool

open PassiveAcousticLocalizationBoundary public

canonicalPassiveAcousticLocalizationBoundary : PassiveAcousticLocalizationBoundary
canonicalPassiveAcousticLocalizationBoundary =
  passive-acoustic-localization-boundary
    true true true true true true true true true false

sceneMixtureOwnerReused : String
sceneMixtureOwnerReused =
  "DASHI.Biology.AnimalCommunicationSceneObservationExact.SignalMixtureObservation"

localizationReading : String
localizationReading =
  "Passive localization uses synchronized microphone geometry, clock calibration and source-relative arrival/phase/level evidence to produce candidate world regions for acoustic events. It can narrow multi-source scene hypotheses without attaching tags or actively probing animals, but a good localization fit does not create species identity, unique individual identity, interaction or semantic meaning."
