module DASHI.Law.SensibLawWoogarooBartyOutreachExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawRuntimeWrongTypeElementFrontierExact as WrongType
import DASHI.Law.SensibLawLegalResidualProducerSchedulerExact as Scheduler
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- WOOGAROO / BARTY OUTREACH AS A SENSIBLAW + WRONGTYPE REGRESSION
--
-- This module does not assert that Ash Barty supports or opposes any
-- development.  It formalises the evidence and consent gates that must be
-- crossed before a Save Woogaroo Forest outreach step can be promoted into a
-- public attribution.
--
-- Core discipline:
--
--   association / local nexus
--     != endorsement
--     != authority
--     != consent to public attribution.
--
-- The point is exactly the WrongType/SensibLaw distinction between a visible
-- relation and the particular typed element required by the downstream
-- consumer.
------------------------------------------------------------------------

data OutreachEvidenceKind : Set where
  publicRoleEvidence : OutreachEvidenceKind
  placeNexusEvidence : OutreachEvidenceKind
  ecologicalSpatialEvidence : OutreachEvidenceKind
  developmentProvenanceEvidence : OutreachEvidenceKind
  campaignBriefingEvidence : OutreachEvidenceKind
  representativeConsentEvidence : OutreachEvidenceKind
  attributablePositionEvidence : OutreachEvidenceKind


data OutreachAsk : Set where
  privateBriefing : OutreachAsk
  privateSiteWalk : OutreachAsk
  communityNatureEvent : OutreachAsk
  proceduralStewardshipStatement : OutreachAsk
  valuesStatement : OutreachAsk
  explicitConservationAdvocacy : OutreachAsk


data OutreachResidual : Set where
  localNexusUnresolved : OutreachResidual
  exactSpatialRelationUnresolved : OutreachResidual
  developmentProvenanceUnresolved : OutreachResidual
  factualBriefingUnresolved : OutreachResidual
  consentUnresolved : OutreachResidual
  attributablePositionUnresolved : OutreachResidual


data OutreachProducer : Set where
  publicProfileSourceProducer : OutreachProducer
  spatialEcologySourceProducer : OutreachProducer
  developmentSourceProducer : OutreachProducer
  campaignBriefProducer : OutreachProducer
  directConsentProducer : OutreachProducer
  directAttributionProducer : OutreachProducer

producerForResidual : OutreachResidual → OutreachProducer
producerForResidual localNexusUnresolved = publicProfileSourceProducer
producerForResidual exactSpatialRelationUnresolved = spatialEcologySourceProducer
producerForResidual developmentProvenanceUnresolved = developmentSourceProducer
producerForResidual factualBriefingUnresolved = campaignBriefProducer
producerForResidual consentUnresolved = directConsentProducer
producerForResidual attributablePositionUnresolved = directAttributionProducer

------------------------------------------------------------------------
-- Source-backed place/provenance receipts.
------------------------------------------------------------------------

record LocalNexusReceipt : Set where
  constructor localNexusReceipt
  field
    person : String
    publicRoleCarrier : String
    localPlace : String
    exactSupportedRelation : String

open LocalNexusReceipt public

record ExactEcologicalSpatialRelation : Set where
  constructor exactEcologicalSpatialRelation
  field
    playgroundCarrier : String
    parklandsCarrier : String
    woogarooCarrier : String
    exactSpatialClaim : String
    sourceCarrier : String

open ExactEcologicalSpatialRelation public

record DevelopmentProvenanceReceipt : Set where
  constructor developmentProvenanceReceipt
  field
    proponent : String
    proposal : String
    affectedLandscape : String
    provenanceCarrier : String
    exactDevelopmentClaim : String

open DevelopmentProvenanceReceipt public

------------------------------------------------------------------------
-- A factual invitation can be admissible without implying any policy view.
------------------------------------------------------------------------

record FactualOutreachBrief : Set where
  constructor factualOutreachBrief
  field
    localNexus : LocalNexusReceipt
    spatialRelation : ExactEcologicalSpatialRelation
    developmentProvenance : DevelopmentProvenanceReceipt
    campaignIdentity : String
    invitationScope : String
    noPredeterminedPosition : Bool
    noPredeterminedPositionIsTrue : noPredeterminedPosition ≡ true

open FactualOutreachBrief public

record AdmissibleOutreachAsk (brief : FactualOutreachBrief) : Set where
  constructor admissibleOutreachAsk
  field
    ask : OutreachAsk
    voluntary : Bool
    voluntaryIsTrue : voluntary ≡ true
    nonMisrepresentative : Bool
    nonMisrepresentativeIsTrue : nonMisrepresentative ≡ true
    conflictAware : Bool
    conflictAwareIsTrue : conflictAware ≡ true
    proportionate : Bool
    proportionateIsTrue : proportionate ≡ true

open AdmissibleOutreachAsk public

------------------------------------------------------------------------
-- Consent is claim-scoped.  A meeting or visit is not consent to attribution.
------------------------------------------------------------------------

record RepresentativeConsentReceipt
    {brief : FactualOutreachBrief}
    (request : AdmissibleOutreachAsk brief) : Set where
  constructor representativeConsentReceipt
  field
    consentingParty : String
    consentCarrier : String
    consentedAsk : OutreachAsk
    consentedAskMatches : consentedAsk ≡ ask request
    consentScope : String

open RepresentativeConsentReceipt public

record PublicAttributionReceipt
    {brief : FactualOutreachBrief}
    {request : AdmissibleOutreachAsk brief}
    (consent : RepresentativeConsentReceipt request) : Set where
  constructor publicAttributionReceipt
  field
    attributableSpeaker : String
    attributableClaim : String
    attributionCarrier : String
    authorisedScope : String
    authorisedScopeMatchesClaim : authorisedScope ≡ attributableClaim

open PublicAttributionReceipt public

------------------------------------------------------------------------
-- Consumer-indexed outreach state.
------------------------------------------------------------------------

data OutreachConsumerGoal : Set where
  permitPrivateInvitation : OutreachConsumerGoal
  establishInformedConsideration : OutreachConsumerGoal
  establishConsentedParticipation : OutreachConsumerGoal
  permitPublicAttribution : OutreachConsumerGoal


data OutreachGoalState : Set where
  goalOpen goalClosed goalBlocked : OutreachGoalState

record OutreachState : Set where
  constructor outreachState
  field
    localNexusPaid : Bool
    spatialRelationPaid : Bool
    developmentProvenancePaid : Bool
    factualBriefPaid : Bool
    consentPaid : Bool
    attributablePositionPaid : Bool

open OutreachState public

privateInvitationReady : OutreachState → Bool
privateInvitationReady s with localNexusPaid s | spatialRelationPaid s | developmentProvenancePaid s | factualBriefPaid s
... | true | true | true | true = true
... | _ | _ | _ | _ = false

consentedParticipationReady : OutreachState → Bool
consentedParticipationReady s with privateInvitationReady s | consentPaid s
... | true | true = true
... | _ | _ = false

publicAttributionReady : OutreachState → Bool
publicAttributionReady s with consentedParticipationReady s | attributablePositionPaid s
... | true | true = true
... | _ | _ = false

goalState : OutreachConsumerGoal → OutreachState → OutreachGoalState
goalState permitPrivateInvitation s with privateInvitationReady s
... | true = goalClosed
... | false = goalOpen
goalState establishInformedConsideration s with privateInvitationReady s
... | true = goalClosed
... | false = goalOpen
goalState establishConsentedParticipation s with consentedParticipationReady s
... | true = goalClosed
... | false = goalOpen
goalState permitPublicAttribution s with publicAttributionReady s
... | true = goalClosed
... | false = goalOpen

------------------------------------------------------------------------
-- First-live-residual scheduler.  Spatial relation is deliberately before
-- campaign promotion: proximity language cannot silently pay ecology.
------------------------------------------------------------------------

firstResidual : OutreachState → OutreachResidual
firstResidual s with localNexusPaid s
... | false = localNexusUnresolved
... | true with spatialRelationPaid s
...   | false = exactSpatialRelationUnresolved
...   | true with developmentProvenancePaid s
...     | false = developmentProvenanceUnresolved
...     | true with factualBriefPaid s
...       | false = factualBriefingUnresolved
...       | true with consentPaid s
...         | false = consentUnresolved
...         | true = attributablePositionUnresolved

nextProducer : OutreachState → OutreachProducer
nextProducer s = producerForResidual (firstResidual s)

------------------------------------------------------------------------
-- WrongType/SensibLaw firewalls.
------------------------------------------------------------------------

data AssociationAutomaticallyEndorsement : Set where
data LocalNexusAutomaticallyPolicyObligation : Set where
data PlaygroundProximityAutomaticallyEcologicalRelation : Set where
data InvitationAutomaticallySupport : Set where
data MeetingAutomaticallySupport : Set where
data SiteVisitAutomaticallyOpposition : Set where
data ConsentToVisitAutomaticallyConsentToQuote : Set where
data SponsorCompatibilityAutomaticallyConsent : Set where
data PublicProfileAutomaticallyAuthority : Set where

associationDoesNotAutoCreateEndorsement :
  AssociationAutomaticallyEndorsement → ⊥
associationDoesNotAutoCreateEndorsement ()

localNexusDoesNotAutoCreatePolicyObligation :
  LocalNexusAutomaticallyPolicyObligation → ⊥
localNexusDoesNotAutoCreatePolicyObligation ()

playgroundProximityDoesNotAutoCreateEcologicalRelation :
  PlaygroundProximityAutomaticallyEcologicalRelation → ⊥
playgroundProximityDoesNotAutoCreateEcologicalRelation ()

invitationDoesNotAutoCreateSupport : InvitationAutomaticallySupport → ⊥
invitationDoesNotAutoCreateSupport ()

meetingDoesNotAutoCreateSupport : MeetingAutomaticallySupport → ⊥
meetingDoesNotAutoCreateSupport ()

siteVisitDoesNotAutoCreateOpposition : SiteVisitAutomaticallyOpposition → ⊥
siteVisitDoesNotAutoCreateOpposition ()

visitConsentDoesNotAutoCreateQuoteConsent :
  ConsentToVisitAutomaticallyConsentToQuote → ⊥
visitConsentDoesNotAutoCreateQuoteConsent ()

sponsorCompatibilityDoesNotAutoCreateConsent :
  SponsorCompatibilityAutomaticallyConsent → ⊥
sponsorCompatibilityDoesNotAutoCreateConsent ()

publicProfileDoesNotAutoCreateAuthority : PublicProfileAutomaticallyAuthority → ⊥
publicProfileDoesNotAutoCreateAuthority ()

------------------------------------------------------------------------
-- Canonical Barty/Woogaroo regression state.
--
-- We intentionally mark the public/local nexus as paid while leaving the exact
-- ecological-spatial relation open.  This captures the current proof-search
-- boundary: the playground/local-place relationship can motivate a search, but
-- it cannot itself prove the required playground <-> parklands <-> Woogaroo
-- ecological relation.
------------------------------------------------------------------------

bartyWoogarooCurrentState : OutreachState
bartyWoogarooCurrentState =
  outreachState
    true
    false
    false
    false
    false
    false

bartyWoogarooFirstResidual :
  firstResidual bartyWoogarooCurrentState ≡ exactSpatialRelationUnresolved
bartyWoogarooFirstResidual = refl

bartyWoogarooNextProducer :
  nextProducer bartyWoogarooCurrentState ≡ spatialEcologySourceProducer
bartyWoogarooNextProducer = refl

record WoogarooBartyWrongTypeBoundary : Set where
  constructor woogarooBartyWrongTypeBoundary
  field
    associationEqualsEndorsement : Bool
    associationEqualsEndorsementIsFalse : associationEqualsEndorsement ≡ false

    placeNexusEqualsSpatialProof : Bool
    placeNexusEqualsSpatialProofIsFalse : placeNexusEqualsSpatialProof ≡ false

    visitEqualsPublicSupport : Bool
    visitEqualsPublicSupportIsFalse : visitEqualsPublicSupport ≡ false

    consentIsClaimScoped : Bool
    consentIsClaimScopedIsTrue : consentIsClaimScoped ≡ true

    proofSearchIsResidualDirected : Bool
    proofSearchIsResidualDirectedIsTrue : proofSearchIsResidualDirected ≡ true

canonicalWoogarooBartyWrongTypeBoundary : WoogarooBartyWrongTypeBoundary
canonicalWoogarooBartyWrongTypeBoundary =
  woogarooBartyWrongTypeBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
