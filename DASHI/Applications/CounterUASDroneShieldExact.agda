module DASHI.Applications.CounterUASDroneShieldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- DEFENSIVE COUNTER-UAS / DRONESHIELD-STYLE ARCHITECTURE
--
-- Scope:
--   sensing -> detection -> association/fusion -> classification/track
--   -> threat assessment -> independent authority/context gate -> response
--
-- This owner deliberately contains no waveform, frequency, power, targeting,
-- or defeat recipe.  It formalises evidence/provenance and the decision gate.
------------------------------------------------------------------------

data SensorModality : Set where
  radioFrequency : SensorModality
  radar : SensorModality
  electroOpticalInfrared : SensorModality
  acoustic : SensorModality
  lidar : SensorModality
  remoteIdentification : SensorModality

data EmitterKnowledge : Set where
  knownEmitter : EmitterKnowledge
  unknownEmitter : EmitterKnowledge
  unresolvedEmitter : EmitterKnowledge

data ClassificationState : Set where
  unclassified : ClassificationState
  candidateUAS : ClassificationState
  classifiedUAS : ClassificationState
  nonUAS : ClassificationState

data AuthorityState : Set where
  noMitigationAuthority : AuthorityState
  mitigationAuthorityGranted : AuthorityState

data ResponseKind : Set where
  observeResponse : ResponseKind
  alertResponse : ResponseKind
  trackResponse : ResponseKind
  cueResponse : ResponseKind
  mitigateResponse : ResponseKind

record OperatingContext : Set where
  constructor operatingContext
  field
    environmentLabel : String
    targetAssumptions : String
    sensorAssumptions : String
    degradationAssumptions : String

open OperatingContext public

record SensorObservation : Set where
  constructor sensorObservation
  field
    observationModality : SensorModality
    observationSource : String
    observationContext : OperatingContext
    observationLabel : String

open SensorObservation public

record FusedTrack : Set where
  constructor fusedTrack
  field
    trackLabel : String
    trackClassification : ClassificationState
    trackEmitterKnowledge : EmitterKnowledge
    trackObservations : List SensorObservation
    observationProvenanceRetained : Bool
    observationProvenanceRetainedIsTrue :
      observationProvenanceRetained ≡ true
    operatingContextRetained : Bool
    operatingContextRetainedIsTrue : operatingContextRetained ≡ true

open FusedTrack public

record ThreatAssessment : Set where
  constructor threatAssessment
  field
    assessedTrack : FusedTrack
    assessmentLabel : String
    assessmentConfidenceLabel : String

open ThreatAssessment public

record MitigationAuthority : Set where
  constructor mitigationAuthority
  field
    authorityActor : String
    authorityJurisdiction : String
    authorityBasis : String
    authorityState : AuthorityState

open MitigationAuthority public

responseFor : ThreatAssessment → MitigationAuthority → ResponseKind
responseFor assessment authority with authorityState authority
... | noMitigationAuthority = observeResponse
... | mitigationAuthorityGranted = mitigateResponse

------------------------------------------------------------------------
-- Explicit no-promotion boundaries.
------------------------------------------------------------------------

passiveRFObservationDoesNotCreateThreatAuthority : Bool
passiveRFObservationDoesNotCreateThreatAuthority = true

detectionDoesNotCreateMitigationAuthority : Bool
detectionDoesNotCreateMitigationAuthority = true

threatAssessmentDoesNotCreateMitigationAuthority : Bool
threatAssessmentDoesNotCreateMitigationAuthority = true

unknownEmitterDoesNotCreateKnownIdentity : Bool
unknownEmitterDoesNotCreateKnownIdentity = true

performanceClaimRequiresOperatingContext : Bool
performanceClaimRequiresOperatingContext = true

fusedTrackRequiresObservationProvenance : Bool
fusedTrackRequiresObservationProvenance = true

manufacturerClaimIsIndependentValidation : Bool
manufacturerClaimIsIndependentValidation = false

academicReviewIsDroneShieldProductValidation : Bool
academicReviewIsDroneShieldProductValidation = false

------------------------------------------------------------------------
-- Query-indexed non-factorability I:
-- the same visible track can require different responses because mitigation
-- authority is an independent coordinate.  Therefore a mitigation decision
-- cannot factor through track state alone.
------------------------------------------------------------------------

data DecisionWorld : Set where
  sameTrackNoAuthority : DecisionWorld
  sameTrackWithAuthority : DecisionWorld

data TrackSurface : Set where
  sameVisibleTrack : TrackSurface

data DecisionQuery : Set where
  trackingQuery : DecisionQuery
  mitigationQuery : DecisionQuery

data DecisionAnswer : Set where
  trackVisible : DecisionAnswer
  observeOnly : DecisionAnswer
  mitigationPermitted : DecisionAnswer

trackOnlyProjection : DecisionWorld → TrackSurface
trackOnlyProjection world = sameVisibleTrack

authorityProjection : DecisionWorld → AuthorityState
authorityProjection sameTrackNoAuthority = noMitigationAuthority
authorityProjection sameTrackWithAuthority = mitigationAuthorityGranted

responseAnswer : DecisionQuery → DecisionWorld → DecisionAnswer
responseAnswer trackingQuery world = trackVisible
responseAnswer mitigationQuery sameTrackNoAuthority = observeOnly
responseAnswer mitigationQuery sameTrackWithAuthority = mitigationPermitted

responseSemantics : Adequacy.QuerySemantics DecisionWorld DecisionQuery DecisionAnswer
responseSemantics = Adequacy.querySemantics responseAnswer

trackOnlyMitigationAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    trackOnlyProjection
    responseSemantics
    mitigationQuery
trackOnlyMitigationAdequacyDefect =
  Adequacy.queryAdequacyDefect
    sameTrackNoAuthority
    sameTrackWithAuthority
    refl
    (λ ())

trackOnlyCannotDetermineMitigation :
  Adequacy.AdequateFor trackOnlyProjection responseSemantics mitigationQuery → ⊥
trackOnlyCannotDetermineMitigation =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    trackOnlyMitigationAdequacyDefect

trackAndAuthorityProjection : DecisionWorld → TrackSurface × AuthorityState
trackAndAuthorityProjection =
  Observer.pairObserver trackOnlyProjection authorityProjection

joinedMitigationAnswer : TrackSurface × AuthorityState → DecisionAnswer
joinedMitigationAnswer (sameVisibleTrack , noMitigationAuthority) = observeOnly
joinedMitigationAnswer (sameVisibleTrack , mitigationAuthorityGranted) = mitigationPermitted

trackAndAuthorityDetermineMitigation :
  Adequacy.AdequateFor
    trackAndAuthorityProjection
    responseSemantics
    mitigationQuery
trackAndAuthorityDetermineMitigation =
  Adequacy.factorsForQuery
    joinedMitigationAnswer
    (λ { sameTrackNoAuthority → refl
       ; sameTrackWithAuthority → refl
       })

trackAndAuthorityStrictlyRefinesTrack :
  Observer.StrictRefinement trackOnlyProjection trackAndAuthorityProjection
trackAndAuthorityStrictlyRefinesTrack =
  Observer.strictPairRefinement
    trackOnlyProjection
    authorityProjection
    sameTrackNoAuthority
    sameTrackWithAuthority
    refl
    (λ ())

------------------------------------------------------------------------
-- Query-indexed non-factorability II:
-- the same supplier/specification surface does not determine actual field
-- performance when environmental/target conditions differ.
------------------------------------------------------------------------

data EvaluationWorld : Set where
  nominalEnvironment : EvaluationWorld
  degradedEnvironment : EvaluationWorld

data SpecificationSurface : Set where
  samePublishedSpecification : SpecificationSurface

data EnvironmentSurface : Set where
  nominalConditions : EnvironmentSurface
  degradedConditions : EnvironmentSurface

data EvaluationQuery : Set where
  supplierSpecificationQuery : EvaluationQuery
  fieldPerformanceQuery : EvaluationQuery

data EvaluationAnswer : Set where
  specificationPresent : EvaluationAnswer
  nominalPerformance : EvaluationAnswer
  degradedPerformance : EvaluationAnswer

specificationProjection : EvaluationWorld → SpecificationSurface
specificationProjection world = samePublishedSpecification

environmentProjection : EvaluationWorld → EnvironmentSurface
environmentProjection nominalEnvironment = nominalConditions
environmentProjection degradedEnvironment = degradedConditions

evaluationAnswer : EvaluationQuery → EvaluationWorld → EvaluationAnswer
evaluationAnswer supplierSpecificationQuery world = specificationPresent
evaluationAnswer fieldPerformanceQuery nominalEnvironment = nominalPerformance
evaluationAnswer fieldPerformanceQuery degradedEnvironment = degradedPerformance

evaluationSemantics :
  Adequacy.QuerySemantics EvaluationWorld EvaluationQuery EvaluationAnswer
evaluationSemantics = Adequacy.querySemantics evaluationAnswer

specificationOnlyPerformanceAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    specificationProjection
    evaluationSemantics
    fieldPerformanceQuery
specificationOnlyPerformanceAdequacyDefect =
  Adequacy.queryAdequacyDefect
    nominalEnvironment
    degradedEnvironment
    refl
    (λ ())

specificationOnlyCannotDetermineFieldPerformance :
  Adequacy.AdequateFor
    specificationProjection
    evaluationSemantics
    fieldPerformanceQuery →
  ⊥
specificationOnlyCannotDetermineFieldPerformance =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    specificationOnlyPerformanceAdequacyDefect

specificationAndEnvironmentProjection :
  EvaluationWorld → SpecificationSurface × EnvironmentSurface
specificationAndEnvironmentProjection =
  Observer.pairObserver specificationProjection environmentProjection

joinedPerformanceAnswer :
  SpecificationSurface × EnvironmentSurface → EvaluationAnswer
joinedPerformanceAnswer (samePublishedSpecification , nominalConditions) =
  nominalPerformance
joinedPerformanceAnswer (samePublishedSpecification , degradedConditions) =
  degradedPerformance

specificationAndEnvironmentDetermineFieldPerformance :
  Adequacy.AdequateFor
    specificationAndEnvironmentProjection
    evaluationSemantics
    fieldPerformanceQuery
specificationAndEnvironmentDetermineFieldPerformance =
  Adequacy.factorsForQuery
    joinedPerformanceAnswer
    (λ { nominalEnvironment → refl
       ; degradedEnvironment → refl
       })

------------------------------------------------------------------------
-- Current public product/legal source coordinates (non-academic authority).
------------------------------------------------------------------------

droneShieldRfAI3Source : String
droneShieldRfAI3Source =
  "DroneShield, RfAI-3 launch, Sydney, 28 July 2026: wideband RF sensing distinguishes known matched emitters from previously unseen emissions and reports confidence"

droneShieldSensorFusionSource : String
droneShieldSensorFusionSource =
  "DroneShield, SensorFusionAI: sensor-agnostic 3D fusion of RF, radar, acoustic and camera outputs with confidence/threat assessment in DroneSentry-C2"

australianMitigationAuthoritySource : String
australianMitigationAuthoritySource =
  "ACMA section 27 exemptions: remotely piloted aircraft disruption equipment is authorised for specified Australian police use; exemption status is a separate coordinate from detection or threat assessment"

record CounterUASDroneShieldBoundary : Set where
  constructor counterUASDroneShieldBoundary
  field
    observationEqualsThreat : Bool
    observationEqualsThreatIsFalse : observationEqualsThreat ≡ false
    detectionEqualsHostility : Bool
    detectionEqualsHostilityIsFalse : detectionEqualsHostility ≡ false
    hostilityEqualsAuthority : Bool
    hostilityEqualsAuthorityIsFalse : hostilityEqualsAuthority ≡ false
    unknownEqualsKnownIdentity : Bool
    unknownEqualsKnownIdentityIsFalse : unknownEqualsKnownIdentity ≡ false
    vendorSpecificationEqualsFieldPerformance : Bool
    vendorSpecificationEqualsFieldPerformanceIsFalse :
      vendorSpecificationEqualsFieldPerformance ≡ false
    fusionMayDiscardProvenance : Bool
    fusionMayDiscardProvenanceIsFalse : fusionMayDiscardProvenance ≡ false

canonicalCounterUASDroneShieldBoundary : CounterUASDroneShieldBoundary
canonicalCounterUASDroneShieldBoundary =
  counterUASDroneShieldBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
