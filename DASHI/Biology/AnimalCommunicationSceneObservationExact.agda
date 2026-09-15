module DASHI.Biology.AnimalCommunicationSceneObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Physics.MultiscaleWaveCorrespondence as WaveCorrespondence

------------------------------------------------------------------------
-- GENERIC MULTI-EMITTER ANIMAL COMMUNICATION SCENES
------------------------------------------------------------------------

data SignalModality : Set where
  acoustic : SignalModality
  visualGesture : SignalModality
  locomotorDisplay : SignalModality
  substrateVibration : SignalModality
  electric : SignalModality
  chemicalOlfactory : SignalModality
  tactileContact : SignalModality
  multimodalComposite : SignalModality
  unresolvedModality : SignalModality

data ParticipantIdentityStatus : Set where
  identityUnknown : ParticipantIdentityStatus
  identityCandidate : ParticipantIdentityStatus
  identitySourceBound : ParticipantIdentityStatus
  identityPaid : ParticipantIdentityStatus

data AssociationStatus : Set where
  associationUnknown : AssociationStatus
  associationCandidate : AssociationStatus
  associationPaid : AssociationStatus
  associationRejected : AssociationStatus

data ObservationDecision : Set where
  candidate : ObservationDecision
  promoted : ObservationDecision
  abstain : ObservationDecision
  rejected : ObservationDecision

record EmitterCandidate : Set where
  constructor emitter-candidate
  field
    participantReference : String
    signalEventReference : String
    speciesIdentityStatus : ParticipantIdentityStatus
    individualIdentityStatus : ParticipantIdentityStatus
    groupIdentityStatus : ParticipantIdentityStatus
    visualTrackIdentityStatus : ParticipantIdentityStatus
    acousticStreamIdentityStatus : ParticipantIdentityStatus
    crossModalAssociationStatus : AssociationStatus
    associationResidualReference : String
    provenanceReference : String
    decision : ObservationDecision

open EmitterCandidate public

------------------------------------------------------------------------
-- Mixture-first acoustic/source propagation layer.
--
-- Cross-pollination is structural only.  ContinuumMaterialLaws owns the
-- distinction Field x Medium -> propagated Field and explicit interference;
-- MultiscaleWaveCorrespondence owns the firewall that a candidate wave model
-- is not automatically a promoted physical law.  This owner reuses those
-- boundaries without claiming a solved acoustic inverse problem.
------------------------------------------------------------------------

record AcousticPropagationReceipt : Set where
  constructor acoustic-propagation-receipt
  field
    sourceFieldReference : String
    propagationMediumReference : String
    boundaryGeometryReference : String
    receiverSensorReference : String
    propagationModelReference : String
    attenuationDispersionReference : String
    reflectionScatteringReference : String
    interferenceReference : String
    calibrationReference : String
    provenanceReference : String
    physicalLawPromotionPaid : Bool

open AcousticPropagationReceipt public

record SignalMixtureObservation : Set where
  constructor signal-mixture-observation
  field
    mixtureId : String
    sceneReference : String
    sensorReference : String
    timeIntervalReference : String
    simultaneousSignalEventReferences : List String
    simultaneousEmitterCandidates : List EmitterCandidate
    candidatePropagationReceipts : List AcousticPropagationReceipt
    unresolvedMixtureResidualReference : String
    manyToManyAVAssociationRetained : Bool
    uniqueSourceDecompositionPaid : Bool
    decision : ObservationDecision
    receiptReferences : List String

open SignalMixtureObservation public

record AnimalCommunicationScene : Set where
  constructor animal-communication-scene
  field
    sceneId : String
    sourceId : String
    sourceTimeReference : String
    physicalTimeReference : String
    environmentReference : String
    observedSurroundsReference : String
    participantReferences : List String
    emitterCandidates : List EmitterCandidate
    overlappingSignalEventReferences : List String
    mixtureObservationReferences : List String
    receiptReferences : List String

open AnimalCommunicationScene public

record SourceAssociationReceipt : Set where
  constructor source-association-receipt
  field
    sceneReference : String
    signalEventReference : String
    candidateEmitterReference : String
    visualTrackReference : String
    sourceStreamReference : String
    associationStatus : AssociationStatus
    residualReference : String
    methodReference : String
    provenanceReference : String

open SourceAssociationReceipt public

------------------------------------------------------------------------
-- Finite evening-chorus obstruction:
-- scene species presence is insufficient to identify which species emitted a
-- particular unresolved event.
------------------------------------------------------------------------

data ChorusState : Set where
  magpieProducedEvent : ChorusState
  lorikeetProducedEvent : ChorusState

data ScenePresenceSurface : Set where
  magpieAndLorikeetPresent : ScenePresenceSurface

data SceneQuery : Set where
  speciesPresentQuery : SceneQuery
  eventEmitterQuery : SceneQuery

data SceneAnswer : Set where
  bothSpeciesPresent : SceneAnswer
  magpieEmitter : SceneAnswer
  lorikeetEmitter : SceneAnswer

scenePresenceProjection : ChorusState → ScenePresenceSurface
scenePresenceProjection state = magpieAndLorikeetPresent

sceneAnswer : SceneQuery → ChorusState → SceneAnswer
sceneAnswer speciesPresentQuery state = bothSpeciesPresent
sceneAnswer eventEmitterQuery magpieProducedEvent = magpieEmitter
sceneAnswer eventEmitterQuery lorikeetProducedEvent = lorikeetEmitter

sceneSemantics : Query.QuerySemantics ChorusState SceneQuery SceneAnswer
sceneSemantics = Query.querySemantics sceneAnswer

speciesPresenceAdequateForPresenceQuery :
  Query.AdequateFor scenePresenceProjection sceneSemantics speciesPresentQuery
speciesPresenceAdequateForPresenceQuery =
  Query.factorsForQuery (λ surface → bothSpeciesPresent) (λ state → refl)

scenePresenceEmitterDefect :
  Query.QueryAdequacyDefect scenePresenceProjection sceneSemantics eventEmitterQuery
scenePresenceEmitterDefect =
  Query.queryAdequacyDefect
    magpieProducedEvent
    lorikeetProducedEvent
    refl
    (λ ())

scenePresenceCannotAssignEmitter :
  Query.AdequateFor scenePresenceProjection sceneSemantics eventEmitterQuery → ⊥
scenePresenceCannotAssignEmitter =
  Query.queryAdequacyDefectBlocksFactorisation scenePresenceEmitterDefect

------------------------------------------------------------------------
-- Finite propagation/inverse obstruction:
-- the same observed sensor mixture may admit different source decompositions.
-- Therefore the measured mixture cannot itself force a unique emitter split.
------------------------------------------------------------------------

data MixtureState : Set where
  sourceDecompositionMagpiePlusLorikeet : MixtureState
  sourceDecompositionTwoMagpies : MixtureState

data SensorMixtureSurface : Set where
  sameObservedSensorMixture : SensorMixtureSurface

data MixtureQuery : Set where
  uniqueEmitterDecompositionQuery : MixtureQuery

data MixtureAnswer : Set where
  magpiePlusLorikeetDecomposition : MixtureAnswer
  twoMagpieDecomposition : MixtureAnswer

sensorMixtureProjection : MixtureState → SensorMixtureSurface
sensorMixtureProjection state = sameObservedSensorMixture

mixtureAnswer : MixtureQuery → MixtureState → MixtureAnswer
mixtureAnswer uniqueEmitterDecompositionQuery sourceDecompositionMagpiePlusLorikeet =
  magpiePlusLorikeetDecomposition
mixtureAnswer uniqueEmitterDecompositionQuery sourceDecompositionTwoMagpies =
  twoMagpieDecomposition

mixtureSemantics : Query.QuerySemantics MixtureState MixtureQuery MixtureAnswer
mixtureSemantics = Query.querySemantics mixtureAnswer

sensorMixtureDecompositionDefect :
  Query.QueryAdequacyDefect
    sensorMixtureProjection mixtureSemantics uniqueEmitterDecompositionQuery
sensorMixtureDecompositionDefect =
  Query.queryAdequacyDefect
    sourceDecompositionMagpiePlusLorikeet
    sourceDecompositionTwoMagpies
    refl
    (λ ())

sensorMixtureCannotDetermineUniqueEmitterDecomposition :
  Query.AdequateFor
    sensorMixtureProjection mixtureSemantics uniqueEmitterDecompositionQuery → ⊥
sensorMixtureCannotDetermineUniqueEmitterDecomposition =
  Query.queryAdequacyDefectBlocksFactorisation sensorMixtureDecompositionDefect

continuumWaveLawOwnerReused : String
continuumWaveLawOwnerReused =
  "DASHI.Physics.Laws.ContinuumMaterialLaws.WaveOpticsAcousticsLaw"

multiscaleWavePromotionBoundaryReused : String
multiscaleWavePromotionBoundaryReused =
  "DASHI.Physics.MultiscaleWaveCorrespondence"

record SceneObservationBoundary : Set where
  constructor scene-observation-boundary
  field
    multipleSimultaneousEmittersAllowed : Bool
    overlappingSignalsNeedNotCollapse : Bool
    sceneContainsSpeciesImpliesSpeciesProducedEvent : Bool
    visualTrackNearbyImpliesAcousticEmitterIdentity : Bool
    loudestSignalImpliesUniqueSender : Bool
    temporalOverlapImpliesInteraction : Bool
    classifierProbabilityCreatesCanonicalSceneTruth : Bool
    unknownEmitterRemainsFirstClass : Bool
    crossModalAssociationNeedsSeparateReceipt : Bool
    unresolvedMixtureRemainsFirstClass : Bool
    sensorMixtureRequiresUniqueDecomposition : Bool
    propagationMediumDoesNotCreateEmitterIdentity : Bool
    interferenceDoesNotCreateInteraction : Bool
    propagationModelDoesNotCreateSemanticMeaning : Bool
    manyToManyAVAssociationRetained : Bool
    waveEquationRequiresBoundaryAndMediumData : Bool
    candidateWaveModelDoesNotCreatePhysicalLaw : Bool

open SceneObservationBoundary public

canonicalSceneObservationBoundary : SceneObservationBoundary
canonicalSceneObservationBoundary =
  scene-observation-boundary
    true true false false false false false true true
    true false true true true true true true

runtimeHandoffReading : String
runtimeHandoffReading =
  "A runtime producer may emit multiple candidate emitters for one signal event, multiple overlapping events for one scene, and unresolved sensor mixtures with many-to-many audiovisual associations. Acoustic source fields propagate through a separately receipted medium/geometry before reaching a sensor; attenuation, dispersion, reflection, scattering and interference can refine source hypotheses but do not create emitter identity, interaction or semantics. Species, individual, visual-track, source-stream and cross-modal association identities remain independently receipted; candidate/promote/abstain/reject governance remains upstream of canonical state."
