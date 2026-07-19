module DASHI.Interop.SensibLawOntologyTopology where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Scope.
--
-- This module is a typed topology for the TiRC/SensibLaw data model.  It
-- separates world records, narrative claims, case framing, normative sources,
-- abstract wrongs, and remedies.  It does not parse text, compute embeddings,
-- resolve identities, or decide that a legal classification is correct.

------------------------------------------------------------------------
-- Six-layer carrier and ownership boundary.

data OntologyLayer : Set where
  worldArtefacts : OntologyLayer
  narrativeClaims : OntologyLayer
  legalEpisodes : OntologyLayer
  normativeSources : OntologyLayer
  wrongsInterestsHarms : OntologyLayer
  valuesRemedies : OntologyLayer

data ProductOwner : Set where
  sharedCore : ProductOwner
  TiRC : ProductOwner
  SensibLaw : ProductOwner
  joint : ProductOwner

layerOwner : OntologyLayer → ProductOwner
layerOwner worldArtefacts = sharedCore
layerOwner narrativeClaims = TiRC
layerOwner legalEpisodes = joint
layerOwner normativeSources = SensibLaw
layerOwner wrongsInterestsHarms = SensibLaw
layerOwner valuesRemedies = SensibLaw

------------------------------------------------------------------------
-- Complete logical table universe for the normalised ontology.
--
-- Constructors denote schema roles, not physical SQL naming requirements.

data OntologyTable : Set where
  coreActor actorAlias actorClass roleMarker : OntologyTable
  relationshipBasis relationshipShape relationshipIntensity actorRelation : OntologyTable
  coreEvent eventClass eventParticipant : OntologyTable
  evidenceItem evidenceDerivation eventEvidence : OntologyTable
  storySegment perspective claim claimEvidence : OntologyTable
  legalCase caseIssue caseEvent caseEventLink : OntologyTable
  legalSystem normSourceCategory legalSource legalSourceAlias : OntologyTable
  provision principle principleSource : OntologyTable
  normAtom : OntologyTable
  wrongType wrongTypeAlias wrongTypeSource : OntologyTable
  valueDimension culturalRegister protectedInterestType : OntologyTable
  wrongTypeProtectedInterest mentalState harmClass wrongTypeHarmClass : OntologyTable
  wrongTypeActorConstraint wrongTypeRelationshipConstraint : OntologyTable
  wrongElement wrongElementRequirement : OntologyTable
  factorType wrongTypeFactorPattern : OntologyTable
  valueFrame wrongTypeValueFrame claimedInterest : OntologyTable
  remedyModality remedyPurpose wrongTypeRemedy : OntologyTable
  wrongTypeRelation : OntologyTable
  eventWrongType harmInstance : OntologyTable
  entityDocument entityMention entityFeature vectorProfile : OntologyTable
  resolutionCandidate canonicalEntityLink : OntologyTable
  provenanceReceipt schemaVersion : OntologyTable

------------------------------------------------------------------------
-- Stable identifiers and shared world records.

record StableId : Set where
  constructor stableId
  field value : String

record Actor : Set where
  constructor actor
  field
    actorId : StableId
    canonicalName : String
    actorClassId : StableId

record Event : Set where
  constructor event
  field
    eventId : StableId
    eventClassId : StableId
    occurredAt : String
    description : String

record EvidenceItem : Set where
  constructor evidence
  field
    evidenceId : StableId
    contentHash : String
    mediaType : String
    capturedAt : String
    provenanceId : StableId

record EventEvidenceLink : Set where
  constructor eventEvidenceLink
  field
    linkedEvent : StableId
    linkedEvidence : StableId
    relation : String

attachEvidence : Event → EvidenceItem → String → EventEvidenceLink
attachEvidence e x r =
  eventEvidenceLink (Event.eventId e) (EvidenceItem.evidenceId x) r

------------------------------------------------------------------------
-- Story and claim layer.  Claims are assertions about world records; they are
-- not silently identified with those records.

record Perspective : Set where
  constructor perspectiveRecord
  field
    perspectiveId : StableId
    speakerId : StableId
    frameLabel : String

record Claim : Set where
  constructor claimRecord
  field
    claimId : StableId
    aboutEvent : StableId
    assertedBy : StableId
    claimText : String
    perspectiveRef : StableId

record CaseFrame : Set where
  constructor caseFrame
  field
    caseId : StableId
    legalSystemId : StableId
    issueId : StableId
    framedEvents : List StableId

------------------------------------------------------------------------
-- Normative source layer.

data NormSourceForm : Set where
  constitution statute regulation caseLaw treaty custom religiousText
    communityRule : NormSourceForm

record LegalSystem : Set where
  constructor legalSystem
  field
    systemId : StableId
    parentSystemId : StableId
    jurisdiction : String
    tradition : String

record LegalSource : Set where
  constructor legalSource
  field
    sourceId : StableId
    sourceSystem : StableId
    sourceForm : NormSourceForm
    canonicalCitation : String
    effectiveFrom : String
    effectiveTo : String

record Principle : Set where
  constructor principle
  field
    principleId : StableId
    principleText : String
    sourceIds : List StableId

------------------------------------------------------------------------
-- Faceted abstract wrong ontology.

data InterestSubjectKind : Set where
  individual child group community state environment ancestors : InterestSubjectKind

data InterestObjectKind : Set where
  body mind property data reputation relationship culture territory ecosystem
    lineage status : InterestObjectKind

data InterestModality : Set where
  integrity useAndEnjoyment control privacy honourMana development
    nonDomination : InterestModality

record ProtectedInterestType : Set where
  constructor protectedInterest
  field
    interestId : StableId
    subjectKind : InterestSubjectKind
    objectKind : InterestObjectKind
    interestModality : InterestModality
    culturalRegisterId : StableId


data Culpability : Set where
  strict negligent reckless intentional mixed : Culpability

record WrongType : Set where
  constructor wrongTypeRecord
  field
    wrongTypeId : StableId
    definingSystem : StableId
    sourceIds : List StableId
    protectedInterestIds : List StableId
    actorConstraintIds : List StableId
    relationshipConstraintIds : List StableId
    culpability : Culpability
    harmClassIds : List StableId
    valueFrameIds : List StableId
    remedyIds : List StableId

------------------------------------------------------------------------
-- Application is fibred by event, system, perspective, and evidence support.
-- One event can therefore carry several non-collapsed interpretations.

data ClassificationStatus : Set where
  suggested contested confirmed rejected : ClassificationStatus

record WrongTypeInterpretation : Set where
  constructor interpretation
  field
    interpretedEvent : StableId
    interpretedAs : StableId
    underSystem : StableId
    underPerspective : StableId
    status : ClassificationStatus
    supportEvidence : List StableId
    confidenceBasis : String

record HarmInstance : Set where
  constructor harm
  field
    harmId : StableId
    harmEvent : StableId
    bearerActor : StableId
    harmedInterest : StableId
    interpretationContext : StableId
    effect : String
    severity : Nat

------------------------------------------------------------------------
-- Explicit graph topology.

data EdgeKind : Set where
  hasEvidence describedIn involves concerns frames appliesTo instantiates
    protects harmedIn authorisedBy extractedAs evaluatedUnder respondsTo
    functionalAnalogue broaderThan narrowerThan inspiredBy conflictsWith
    sameAsCandidate : EdgeKind

record OntologyEdge : Set where
  constructor edge
  field
    edgeId : StableId
    fromId : StableId
    edgeKind : EdgeKind
    toId : StableId
    provenanceRef : StableId

------------------------------------------------------------------------
-- Wikitology/KBP translation layer.
--
-- Lexical and semantic evidence are stored as typed observations.  A candidate
-- is not a canonical identity link until a separate decision accepts it.

data FeatureKind : Set where
  exactName fuzzyName longestName characterNGram contextTerms ontologyTags
    articleVector categoryVector topSense multimodalAlignment : FeatureKind

record FeatureObservation : Set where
  constructor featureObservation
  field
    featureKind : FeatureKind
    scoreNumerator : Nat
    scoreDenominator : Nat
    evidenceRef : StableId

record EntityDocument : Set where
  constructor entityDocumentRecord
  field
    entityDocumentId : StableId
    canonicalLabel : String
    entityType : String
    aliases : List String
    contextTerms : List String
    ontologyTagIds : List StableId
    provenanceRefs : List StableId

record ResolutionCandidate : Set where
  constructor resolutionCandidateRecord
  field
    leftEntityDocument : StableId
    rightEntityDocument : StableId
    observations : List FeatureObservation
    decisionStatus : ClassificationStatus

------------------------------------------------------------------------
-- Worked topology witness: the same event is interpreted under two systems.

exampleEventId : StableId
exampleEventId = stableId "event:elder-insult:1"

tikangaSystemId : StableId
tikangaSystemId = stableId "NZ.TIKANGA"

auSystemId : StableId
auSystemId = stableId "AU.COMMON"

manaWrongId : StableId
manaWrongId = stableId "wrong:tikanga:mana-harm"

verbalContextId : StableId
verbalContextId = stableId "wrong:au:verbal-context-only"

userPerspectiveId : StableId
userPerspectiveId = stableId "perspective:user"

tikangaInterpretation : WrongTypeInterpretation
tikangaInterpretation =
  interpretation exampleEventId manaWrongId tikangaSystemId userPerspectiveId
    suggested [] "source, relationship, mana-interest and contextual features"

auInterpretation : WrongTypeInterpretation
auInterpretation =
  interpretation exampleEventId verbalContextId auSystemId userPerspectiveId
    contested [] "same event; different system and actionability boundary"

same-event-multi-system :
  WrongTypeInterpretation.interpretedEvent tikangaInterpretation
  ≡ WrongTypeInterpretation.interpretedEvent auInterpretation
same-event-multi-system = refl

------------------------------------------------------------------------
-- Boundary receipt: statements this module intentionally does not promote.

nonClaimBoundary : List String
nonClaimBoundary =
  "A similarity score is evidence for a resolution candidate, not proof of identity"
  ∷ "A claim is an assertion about an event, not the event itself"
  ∷ "A case is a framing container over events and claims, not a stage after claim"
  ∷ "Evidence attaches to events, claims and case issues; it is not the tail of a linear chain"
  ∷ "WrongType application is indexed by legal system and perspective"
  ∷ "Cross-system functional analogy does not assert doctrinal equivalence"
  ∷ "NLP, embeddings and database migrations remain runtime obligations"
  ∷ []
