module DASHI.Culture.WitchRelationalAttributionDialogueBidiExact where

------------------------------------------------------------------------
-- WITCH RELATIONAL ATTRIBUTION / DIALOGUE / AUTHORITY BIDI
--
-- Same lexical predicate, different relational grammar:
--   "I am a witch"
--   "You are a witch"
--   "She was a witch"
-- do not carry the same authority, provenance, temporal or evidential status.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact as Self
import DASHI.Culture.SymbolicInversionAuthorityTransferBidiExact as Symbol

------------------------------------------------------------------------
-- 1. Relational attribution modes.
------------------------------------------------------------------------

data AttributionPerson : Set where firstPerson secondPerson thirdPerson : AttributionPerson

data AttributionMode : Set where
  selfIdentification
  directExternalAttribution
  accusation
  reportedQuotation
  retrospectiveHistoricalClassification
  reclaimedQuotation
  hostileLabelling
  descriptiveObservation
  : AttributionMode

data AttributionAuthority : Set where
  selfAuthority
  targetContestableAuthority
  institutionalAuthority
  documentaryAuthority
  historianInterpretiveAuthority
  communityAuthority
  unresolvedAuthority
  : AttributionAuthority

data TemporalRelation : Set where presentTime pastTime quotedTime unresolvedTime : TemporalRelation

record RelationalAttribution : Set where
  constructor relational-attribution
  field
    surface : String
    grammaticalPerson : AttributionPerson
    mode : AttributionMode
    authority : AttributionAuthority
    temporalRelation : TemporalRelation
    speaker : String
    target : String
    provenance : String
    contestableByTarget : Bool

open RelationalAttribution public

selfWitch : RelationalAttribution
selfWitch = relational-attribution
  "I am a witch."
  firstPerson selfIdentification selfAuthority presentTime
  "speaker" "speaker"
  "finite DASHI self-identification specimen"
  true

youWitch : RelationalAttribution
youWitch = relational-attribution
  "You are a witch."
  secondPerson directExternalAttribution targetContestableAuthority presentTime
  "external speaker" "addressed person"
  "finite DASHI external-attribution specimen; does not establish target assent"
  true

historicalWitch : RelationalAttribution
historicalWitch = relational-attribution
  "She was a witch."
  thirdPerson retrospectiveHistoricalClassification historianInterpretiveAuthority pastTime
  "later speaker/historian" "historical person"
  "finite DASHI retrospective-classification specimen; requires independent historical evidence"
  false

------------------------------------------------------------------------
-- 2. Same predicate token cannot recover relational mode.
------------------------------------------------------------------------

data RelationalWitchState : Set where
  selfUse externalUse historicalUse : RelationalWitchState

data WitchPredicateSurface : Set where witchPredicate : WitchPredicateSurface

data RelationalModeCode : Set where selfCode externalCode historicalCode : RelationalModeCode

predicateSurface : RelationalWitchState → WitchPredicateSurface
predicateSurface selfUse = witchPredicate
predicateSurface externalUse = witchPredicate
predicateSurface historicalUse = witchPredicate

modeCode : RelationalWitchState → RelationalModeCode
modeCode selfUse = selfCode
modeCode externalUse = externalCode
modeCode historicalUse = historicalCode

selfAndExternalDiffer : modeCode selfUse ≡ modeCode externalUse → ⊥
selfAndExternalDiffer ()

samePredicateCannotRecoverRelationalMode : INF.FactorsThrough predicateSurface modeCode → ⊥
samePredicateCannotRecoverRelationalMode =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness selfUse externalUse refl selfAndExternalDiffer)

------------------------------------------------------------------------
-- 3. Authority is position-sensitive.
------------------------------------------------------------------------

data SelfIdentificationPromotesExternalClassificationAuthority : Set where
data ExternalAttributionPromotesTargetAssent : Set where
data AccusationPromotesHistoricalFact : Set where
data HistoricalRecordPromotesSelfIdentification : Set where
data QuotationPromotesSpeakerEndorsement : Set where
data ReclaimedQuotationPromotesOriginalMeaning : Set where
data HostileLabelPromotesPrivateIdentity : Set where

selfIdentificationDoesNotPromoteExternalClassificationAuthority :
  SelfIdentificationPromotesExternalClassificationAuthority → ⊥
selfIdentificationDoesNotPromoteExternalClassificationAuthority ()

externalAttributionDoesNotPromoteTargetAssent : ExternalAttributionPromotesTargetAssent → ⊥
externalAttributionDoesNotPromoteTargetAssent ()

accusationDoesNotPromoteHistoricalFact : AccusationPromotesHistoricalFact → ⊥
accusationDoesNotPromoteHistoricalFact ()

historicalRecordDoesNotPromoteSelfIdentification : HistoricalRecordPromotesSelfIdentification → ⊥
historicalRecordDoesNotPromoteSelfIdentification ()

quotationDoesNotPromoteSpeakerEndorsement : QuotationPromotesSpeakerEndorsement → ⊥
quotationDoesNotPromoteSpeakerEndorsement ()

reclaimedQuotationDoesNotPromoteOriginalMeaning : ReclaimedQuotationPromotesOriginalMeaning → ⊥
reclaimedQuotationDoesNotPromoteOriginalMeaning ()

hostileLabelDoesNotPromotePrivateIdentity : HostileLabelPromotesPrivateIdentity → ⊥
hostileLabelDoesNotPromotePrivateIdentity ()

------------------------------------------------------------------------
-- 4. PNF obligations differ by relational mode.
------------------------------------------------------------------------

data AttributionObligationKind : Set where
  speakerIdentityObligation
  targetIdentityObligation
  targetAssentObligation
  attributionSourceObligation
  historicalEvidenceObligation
  quotationFidelityObligation
  endorsementObligation
  temporalScopeObligation
  contestabilityObligation
  selfIdentificationObligation
  : AttributionObligationKind

data AttributionStatus : Set where
  recovered
  requiresIndependentReceipt
  unresolved
  notApplicable
  nonidentifiable
  : AttributionStatus

record AttributionAudit : Set where
  constructor attribution-audit
  field
    obligation : AttributionObligationKind
    status : AttributionStatus
    reason : String

open AttributionAudit public

selfIdentificationAuthorityStatus : AttributionStatus
selfIdentificationAuthorityStatus = recovered

externalTargetAssentStatus : AttributionStatus
externalTargetAssentStatus = nonidentifiable

historicalSelfIdentificationStatus : AttributionStatus
historicalSelfIdentificationStatus = requiresIndependentReceipt

------------------------------------------------------------------------
-- 5. Dialogue: reply/contest does not retroactively alter provenance.
------------------------------------------------------------------------

data DialogueMove : Set where
  attributionMove
  acceptanceMove
  rejectionMove
  qualificationMove
  reclaimingMove
  quotationMove
  : DialogueMove

record AttributionDialogue : Set where
  constructor attribution-dialogue
  field
    initial : RelationalAttribution
    response : DialogueMove
    initialProvenancePreserved : Bool
    responseCreatesNewProvenance : Bool

canonicalContestedAttribution : AttributionDialogue
canonicalContestedAttribution = attribution-dialogue
  youWitch rejectionMove true true

canonicalReclaimedAttribution : AttributionDialogue
canonicalReclaimedAttribution = attribution-dialogue
  youWitch reclaimingMove true true

------------------------------------------------------------------------
-- 6. Weld to self-identification and symbolic-inversion owners.
------------------------------------------------------------------------

record WitchRelationalAttributionWeld : Set where
  constructor witch-relational-attribution-weld
  field
    selfBoundary : Self.WitchSelfIdentificationBoundary
    symbolicBoundary : Symbol.SymbolicInversionAuthorityTransferBoundary
    relationalModeNonfactorability : INF.FactorsThrough predicateSurface modeCode → ⊥

canonicalWitchRelationalAttributionWeld : WitchRelationalAttributionWeld
canonicalWitchRelationalAttributionWeld =
  witch-relational-attribution-weld
    Self.canonicalWitchSelfIdentificationBoundary
    Symbol.canonicalSymbolicInversionAuthorityTransferBoundary
    samePredicateCannotRecoverRelationalMode

record WitchRelationalAttributionBoundary : Set where
  constructor witch-relational-attribution-boundary
  field
    samePredicateMeansSameRelationalAct : Bool
    firstPersonEqualsThirdPersonAuthority : Bool
    externalLabelEqualsTargetAssent : Bool
    accusationEqualsHistoricalFact : Bool
    historicalClassificationEqualsHistoricalSelfIdentification : Bool
    quotationEqualsEndorsement : Bool
    reclamationRewritesOriginalMeaning : Bool
    hostileLabelRecoversPrivateIdentity : Bool
    targetResponseErasesInitialProvenance : Bool
    relationalModeRequiresIndependentCoordinates : Bool

canonicalWitchRelationalAttributionBoundary : WitchRelationalAttributionBoundary
canonicalWitchRelationalAttributionBoundary =
  witch-relational-attribution-boundary
    false false false false false false false false false true
