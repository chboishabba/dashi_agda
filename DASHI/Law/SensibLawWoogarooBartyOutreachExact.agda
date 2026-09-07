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
-- Source-backed receipts.
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

record DevelopmentProvenanceBundle : Set where
  constructor developmentProvenanceBundle
  field
    peninsula : DevelopmentProvenanceReceipt
    scenic : DevelopmentProvenanceReceipt

open DevelopmentProvenanceBundle public

------------------------------------------------------------------------
-- Concrete current source receipts.
--
-- Scope is intentionally narrow.  The spatial receipt proves hydrological /
-- ecological-system membership through Council carriers.  It does NOT prove
-- that every named development footprint is adjacent to the playground, nor
-- that Ash Barty holds a view about any proposal.
------------------------------------------------------------------------

bartyPlaygroundLocalNexus : LocalNexusReceipt
bartyPlaygroundLocalNexus =
  localNexusReceipt
    "Ash Barty"
    "Queensland Government media statement 21 March 2025; playground co-designed with Ash Barty and delivered with Ipswich City Council and Springfield City Group"
    "Greater Springfield / Opossum Creek Parklands community"
    "Ash Barty has a direct public community nexus to the playground project and Greater Springfield"

opossumWoogarooSpatialReceipt : ExactEcologicalSpatialRelation
opossumWoogarooSpatialReceipt =
  exactEcologicalSpatialRelation
    "Ash Barty Playground / Opossum Creek Parklands project carrier"
    "Ipswich City Council: Opossum Creek Parklands, 58 Scoparia Drive, Brookwater"
    "Ipswich City Council: Woogaroo Creek sub-catchment including Opossum Creek"
    "Opossum Creek Parklands lies on the Opossum Creek system; Opossum Creek is a tributary within the Woogaroo Creek sub-catchment, and Council identifies significant natural vegetation and wildlife linkages along both Opossum and Woogaroo Creeks"
    "Ipswich City Council Brisbane River Catchment page; Ipswich Planning Scheme Area 4 valuable-features statement; City of Ipswich Platypus Recovery Plan 2020"

peninsulaDevelopmentReceipt : DevelopmentProvenanceReceipt
peninsulaDevelopmentReceipt =
  developmentProvenanceReceipt
    "Springfield City Group"
    "Peninsula Precinct, Springfield, Queensland; EPBC 2020/8629"
    "Springfield / Woogaroo campaign landscape"
    "National EPA / EPBC Act Public Portal"
    "Peninsula Precinct is an EPBC-referred Springfield project under assessment; campaign attribution to Woogaroo is kept separate from the federal project-status fact"

scenicDevelopmentReceipt : DevelopmentProvenanceReceipt
scenicDevelopmentReceipt =
  developmentProvenanceReceipt
    "Springfield City Group Pty Ltd"
    "Scenic Precinct, Springfield, Queensland; EPBC 2020/8651"
    "Springfield / Woogaroo campaign landscape"
    "National EPA / EPBC Act Public Portal preliminary documentation"
    "Springfield City Group seeks EPBC approval for Scenic Precinct at Springfield College Drive; listed threatened species and communities are controlling provisions"

currentDevelopmentProvenance : DevelopmentProvenanceBundle
currentDevelopmentProvenance =
  developmentProvenanceBundle peninsulaDevelopmentReceipt scenicDevelopmentReceipt

------------------------------------------------------------------------
-- A factual invitation can be admissible without implying any policy view.
------------------------------------------------------------------------

record FactualOutreachBrief : Set where
  constructor factualOutreachBrief
  field
    localNexus : LocalNexusReceipt
    spatialRelation : ExactEcologicalSpatialRelation
    developmentProvenance : DevelopmentProvenanceBundle
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
-- Current factual brief and safest initial ask.
------------------------------------------------------------------------

currentFactualBrief : FactualOutreachBrief
currentFactualBrief =
  factualOutreachBrief
    bartyPlaygroundLocalNexus
    opossumWoogarooSpatialReceipt
    currentDevelopmentProvenance
    "Save Woogaroo Forest"
    "Private factual briefing and optional private site walk; no endorsement or public statement requested"
    true
    refl

currentPrivateSiteWalkAsk : AdmissibleOutreachAsk currentFactualBrief
currentPrivateSiteWalkAsk =
  admissibleOutreachAsk
    privateSiteWalk
    true refl
    true refl
    true refl
    true refl

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
data SameCatchmentAutomaticallyFootprintAdjacency : Set where
data InvitationAutomaticallySupport : Set where
data MeetingAutomaticallySupport : Set where
data SiteVisitAutomaticallyOpposition : Set where
data ConsentToVisitAutomaticallyConsentToQuote : Set where
data SponsorCompatibilityAutomaticallyConsent : Set where
data PublicProfileAutomaticallyAuthority : Set where

associationDoesNotAutoCreateEndorsement : AssociationAutomaticallyEndorsement → ⊥
associationDoesNotAutoCreateEndorsement ()

localNexusDoesNotAutoCreatePolicyObligation : LocalNexusAutomaticallyPolicyObligation → ⊥
localNexusDoesNotAutoCreatePolicyObligation ()

playgroundProximityDoesNotAutoCreateEcologicalRelation : PlaygroundProximityAutomaticallyEcologicalRelation → ⊥
playgroundProximityDoesNotAutoCreateEcologicalRelation ()

sameCatchmentDoesNotAutoCreateFootprintAdjacency : SameCatchmentAutomaticallyFootprintAdjacency → ⊥
sameCatchmentDoesNotAutoCreateFootprintAdjacency ()

invitationDoesNotAutoCreateSupport : InvitationAutomaticallySupport → ⊥
invitationDoesNotAutoCreateSupport ()

meetingDoesNotAutoCreateSupport : MeetingAutomaticallySupport → ⊥
meetingDoesNotAutoCreateSupport ()

siteVisitDoesNotAutoCreateOpposition : SiteVisitAutomaticallyOpposition → ⊥
siteVisitDoesNotAutoCreateOpposition ()

visitConsentDoesNotAutoCreateQuoteConsent : ConsentToVisitAutomaticallyConsentToQuote → ⊥
visitConsentDoesNotAutoCreateQuoteConsent ()

sponsorCompatibilityDoesNotAutoCreateConsent : SponsorCompatibilityAutomaticallyConsent → ⊥
sponsorCompatibilityDoesNotAutoCreateConsent ()

publicProfileDoesNotAutoCreateAuthority : PublicProfileAutomaticallyAuthority → ⊥
publicProfileDoesNotAutoCreateAuthority ()

------------------------------------------------------------------------
-- Canonical Barty/Woogaroo state after source payment.
------------------------------------------------------------------------

bartyWoogarooCurrentState : OutreachState
bartyWoogarooCurrentState =
  outreachState
    true
    true
    true
    true
    false
    false

bartyWoogarooFirstResidual :
  firstResidual bartyWoogarooCurrentState ≡ consentUnresolved
bartyWoogarooFirstResidual = refl

bartyWoogarooNextProducer :
  nextProducer bartyWoogarooCurrentState ≡ directConsentProducer
bartyWoogarooNextProducer = refl

bartyWoogarooPrivateInvitationPermitted :
  goalState permitPrivateInvitation bartyWoogarooCurrentState ≡ goalClosed
bartyWoogarooPrivateInvitationPermitted = refl

bartyWoogarooPublicAttributionStillOpen :
  goalState permitPublicAttribution bartyWoogarooCurrentState ≡ goalOpen
bartyWoogarooPublicAttributionStillOpen = refl

record WoogarooBartyWrongTypeBoundary : Set where
  constructor woogarooBartyWrongTypeBoundary
  field
    associationEqualsEndorsement : Bool
    associationEqualsEndorsementIsFalse : associationEqualsEndorsement ≡ false
    sameCatchmentEqualsFootprintAdjacency : Bool
    sameCatchmentEqualsFootprintAdjacencyIsFalse : sameCatchmentEqualsFootprintAdjacency ≡ false
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
