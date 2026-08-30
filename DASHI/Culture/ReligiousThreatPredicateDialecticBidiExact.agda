module DASHI.Culture.ReligiousThreatPredicateDialecticBidiExact where

------------------------------------------------------------------------
-- RELIGIOUS THREAT PREDICATE / DIALECTICAL BIDI ADAPTER
--
-- Canonical generic pattern sources currently live on PR #650:
--   DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact
--   DASHI.Reasoning.DialecticalOppositionNonExplosionExact
--
-- This branch does not clone those generic owners.  Instead this adapter
-- instantiates their decomposition discipline locally so that, once #650 is
-- merged, the local records can be replaced by direct imports without changing
-- the domain semantics below.
--
-- Test utterance:
--   "If you do X, you're going to hell."
--
-- The utterance is treated as a compound conditional-sanction assertion, not
-- as one atomic proposition and not as proof that the consequence is true,
-- false, effective, coercive or universally believed by a religious group.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation
import DASHI.Culture.ChildReligiousEpistemicReopeningBidiExact as Reopening
import DASHI.Culture.ReligiousPowerChildFearClaimBidiExact as ClaimAudit

------------------------------------------------------------------------
-- 1. PNF-style decomposition of a conditional sanction claim.
------------------------------------------------------------------------

data ConditionalRole : Set where
  antecedentRole
  consequenceRole
  authorityRole
  targetRole
  sanctionRole
  modalityRole
  temporalRole
  contextRole : ConditionalRole

record ConditionalPredicateAtom : Set where
  constructor conditional-predicate-atom
  field
    atomName : String
    role : ConditionalRole
    domain : String
    reading : String

open ConditionalPredicateAtom public

record ConditionalThreatAssertion : Set where
  constructor conditional-threat-assertion
  field
    assertionKey : String
    naturalLanguage : String
    antecedent : String
    consequence : String
    assertedAuthority : String
    target : String
    context : String
    predicates : List ConditionalPredicateAtom
    provenance : String

open ConditionalThreatAssertion public

hellThreatPredicates : List ConditionalPredicateAtom
hellThreatPredicates =
  conditional-predicate-atom
    "does-X" antecedentRole "person × action"
    "the addressed person performs the specified act X"
  ∷ conditional-predicate-atom
    "goes-to-hell" consequenceRole "person × post-mortem consequence"
    "the person is asserted to undergo the named post-mortem consequence"
  ∷ conditional-predicate-atom
    "conditional-link" modalityRole "antecedent × consequence"
    "the consequence is asserted conditionally on the act"
  ∷ conditional-predicate-atom
    "speaker-authority" authorityRole "speaker × doctrine × target"
    "the utterance may invoke personal, familial, clerical, scriptural or institutional authority"
  ∷ conditional-predicate-atom
    "sanction" sanctionRole "consequence × target"
    "the consequence functions as a threatened or warned-about sanction in the utterance"
  ∷ conditional-predicate-atom
    "audience" targetRole "speaker × child/person"
    "the assertion is addressed to a particular audience whose developmental and dependency state matters"
  ∷ conditional-predicate-atom
    "formation-context" contextRole "family × institution × doctrine × time"
    "the utterance occurs in a situated relational and doctrinal context"
  ∷ []

hellThreatAssertion : ConditionalThreatAssertion
hellThreatAssertion = conditional-threat-assertion
  "religious-threat-if-x-then-hell"
  "If you do X, you're going to hell."
  "you do X"
  "you go to hell"
  "speaker/invoked religious authority unresolved until separately receipted"
  "addressed person; developmental status unresolved in the bare utterance"
  "religious/familial/institutional context unresolved in the bare utterance"
  hellThreatPredicates
  "finite DASHI PNF-style specimen; natural-language example, not an empirical claim that any religion or group universally uses this wording"

------------------------------------------------------------------------
-- 2. Separate proof obligations.  The surface sentence does not discharge
--    the obligations it itself contains.
------------------------------------------------------------------------

data ThreatObligationKind : Set where
  antecedentMeaningObligation
  consequenceDoctrineObligation
  conditionalLinkObligation
  authorityProvenanceObligation
  authorityScopeObligation
  targetDevelopmentObligation
  targetDependencyObligation
  threatComprehensionObligation
  experiencedFearObligation
  behaviourEffectObligation
  belongingPenaltyObligation
  practicalExitObligation
  enduringOutcomeObligation
  truthStatusObligation
  legalClassificationObligation : ThreatObligationKind

record ThreatObligation : Set where
  constructor threat-obligation
  field
    parentAssertion : ConditionalThreatAssertion
    obligationKind : ThreatObligationKind
    obligationReading : String

open ThreatObligation public

data ThreatObligationStatus : Set where
  discharged
  partiallyDischarged
  unresolved
  contradictedAtSameScope
  notEmpiricallyTestableHere
  requiresIndependentReceipt : ThreatObligationStatus

record ThreatObligationAudit : Set where
  constructor threat-obligation-audit
  field
    obligation : ThreatObligation
    status : ThreatObligationStatus
    receipt : String
    reason : String

open ThreatObligationAudit public

hellDoctrineObligation : ThreatObligation
hellDoctrineObligation = threat-obligation hellThreatAssertion
  consequenceDoctrineObligation
  "identify the specific doctrine/interpretive rule that connects X with hell"

hellTruthObligation : ThreatObligation
hellTruthObligation = threat-obligation hellThreatAssertion
  truthStatusObligation
  "the utterance itself does not establish the metaphysical truth or falsity of the asserted consequence"

hellFearObligation : ThreatObligation
hellFearObligation = threat-obligation hellThreatAssertion
  experiencedFearObligation
  "establish whether this recipient understood the assertion and experienced fear"

hellAuthorityObligation : ThreatObligation
hellAuthorityObligation = threat-obligation hellThreatAssertion
  authorityProvenanceObligation
  "identify whether authority is personal, familial, clerical, scriptural, institutional or another source"

hellExitObligation : ThreatObligation
hellExitObligation = threat-obligation hellThreatAssertion
  practicalExitObligation
  "establish whether disagreement/refusal/exit was practically available without material or belonging penalty"

canonicalHellThreatAudit : List ThreatObligationAudit
canonicalHellThreatAudit =
  threat-obligation-audit hellDoctrineObligation unresolved
    "no doctrine-specific receipt installed by the bare utterance"
    "conditional wording alone does not identify which theological interpretation supplies the consequence"
  ∷ threat-obligation-audit hellTruthObligation notEmpiricallyTestableHere
    "no metaphysical truth receipt is manufactured by PNF decomposition"
    "audit of assertion structure is distinct from establishing the asserted afterlife consequence"
  ∷ threat-obligation-audit hellFearObligation requiresIndependentReceipt
    "requires recipient-specific comprehension/fear evidence"
    "threat representation is not identical to experienced fear"
  ∷ threat-obligation-audit hellAuthorityObligation unresolved
    "requires provenance of the invoked authority"
    "speaker status and institutional authority are independent coordinates"
  ∷ threat-obligation-audit hellExitObligation requiresIndependentReceipt
    "requires relational/material exit and belonging-penalty evidence"
    "a warning can be severe without thereby proving entrapment or coercion"
  ∷ []

------------------------------------------------------------------------
-- 3. Dialectical modes.  Counterposition, logical negation and contextual
--    disagreement must not be treated as the same operation.
------------------------------------------------------------------------

data ThreatOppositionMode : Set where
  logicalNegation
  doctrinalCounterclaim
  ethicalCounterposition
  contextualQualification
  authorityChallenge
  refusalPosition : ThreatOppositionMode

logicalNegationNotEthicalCounterposition :
  logicalNegation ≡ ethicalCounterposition → ⊥
logicalNegationNotEthicalCounterposition ()

doctrinalCounterclaimNotLogicalNegation :
  doctrinalCounterclaim ≡ logicalNegation → ⊥
doctrinalCounterclaimNotLogicalNegation ()

authorityChallengeNotLogicalNegation :
  authorityChallenge ≡ logicalNegation → ⊥
authorityChallengeNotLogicalNegation ()

record ThreatPosition : Set where
  constructor threat-position
  field
    wording : String
    mode : ThreatOppositionMode
    contextLabel : String

open ThreatPosition public

originalThreatPosition : ThreatPosition
originalThreatPosition = threat-position
  "If you do X, you're going to hell."
  contextualQualification
  "original assertion under an unresolved religious/relational frame"

logicalNegationPosition : ThreatPosition
logicalNegationPosition = threat-position
  "It is not the case that doing X entails going to hell."
  logicalNegation
  "logical negation of the conditional consequence at the same declared scope"

doctrinalAlternativePosition : ThreatPosition
doctrinalAlternativePosition = threat-position
  "Within another theological interpretation, doing X is not classified as entailing hell."
  doctrinalCounterclaim
  "different doctrinal frame; not automatically P × not-P in one frame"

ethicalCounterpositionExample : ThreatPosition
ethicalCounterpositionExample = threat-position
  "Even if a tradition teaches this consequence, threatening a dependent child with it may require separate ethical justification."
  ethicalCounterposition
  "normative counterposition; not a truth-functional negation of the afterlife proposition"

authorityChallengeExample : ThreatPosition
authorityChallengeExample = threat-position
  "What warrants this speaker's authority to assert that consequence?"
  authorityChallenge
  "provenance/authority challenge; not the proposition's logical negation"

------------------------------------------------------------------------
-- 4. Epistemic status is ternary/non-binary.  Unresolved is not refutation.
------------------------------------------------------------------------

data ThreatClaimComponent : Set where
  conditionalDoctrineComponent
  speakerAuthorityComponent
  recipientFearComponent
  coerciveEffectComponent
  metaphysicalTruthComponent : ThreatClaimComponent

componentStatus : ThreatClaimComponent → Epistemic.EpistemicTrit
componentStatus conditionalDoctrineComponent = Epistemic.unresolved
componentStatus speakerAuthorityComponent = Epistemic.unresolved
componentStatus recipientFearComponent = Epistemic.unresolved
componentStatus coerciveEffectComponent = Epistemic.unresolved
componentStatus metaphysicalTruthComponent = Epistemic.unresolved

data UnresolvedPromotesFalse : Set where

unresolvedDoesNotPromoteFalse : UnresolvedPromotesFalse → ⊥
unresolvedDoesNotPromoteFalse ()

------------------------------------------------------------------------
-- 5. Pressure / coercion decomposition.
------------------------------------------------------------------------

record ThreatActuationContext : Set where
  constructor threat-actuation-context
  field
    developmentalDependence : Bool
    authorityAsymmetry : Bool
    recipientUnderstoodThreat : Bool
    recipientExperiencedFear : Bool
    refusalPenalised : Bool
    belongingPenaltyPresent : Bool
    alternativesRestricted : Bool
    practicalExitRestricted : Bool
    behaviourChanged : Bool

open ThreatActuationContext public

bareUtteranceContext : ThreatActuationContext
bareUtteranceContext = threat-actuation-context
  false false false false false false false false false

candidatePressureContext : ThreatActuationContext
candidatePressureContext = threat-actuation-context
  true true true true true true true true true

record ThreatPressureCandidate (c : ThreatActuationContext) : Set where
  constructor threat-pressure-candidate
  field
    developmentalDependencePresent : developmentalDependence c ≡ true
    authorityAsymmetryPresent : authorityAsymmetry c ≡ true
    understood : recipientUnderstoodThreat c ≡ true
    fearPresent : recipientExperiencedFear c ≡ true
    refusalPenaltyPresent : refusalPenalised c ≡ true
    belongingPenaltyWitness : belongingPenaltyPresent c ≡ true
    exitRestrictionPresent : practicalExitRestricted c ≡ true

open ThreatPressureCandidate public

candidatePressureWitness : ThreatPressureCandidate candidatePressureContext
candidatePressureWitness = threat-pressure-candidate
  refl refl refl refl refl refl refl

data BareUtterancePromotesPressureCandidate : Set where

data PressureCandidatePromotesEntrapment : Set where

data PressureCandidatePromotesLegalCoercion : Set where

data ThreatTruthPromotesBehaviourEffect : Set where

data BehaviourEffectPromotesThreatTruth : Set where

bareUtteranceDoesNotPromotePressureCandidate :
  BareUtterancePromotesPressureCandidate → ⊥
bareUtteranceDoesNotPromotePressureCandidate ()

pressureCandidateDoesNotPromoteEntrapment :
  PressureCandidatePromotesEntrapment → ⊥
pressureCandidateDoesNotPromoteEntrapment ()

pressureCandidateDoesNotPromoteLegalCoercion :
  PressureCandidatePromotesLegalCoercion → ⊥
pressureCandidateDoesNotPromoteLegalCoercion ()

threatTruthDoesNotPromoteBehaviourEffect : ThreatTruthPromotesBehaviourEffect → ⊥
threatTruthDoesNotPromoteBehaviourEffect ()

behaviourEffectDoesNotPromoteThreatTruth : BehaviourEffectPromotesThreatTruth → ⊥
behaviourEffectDoesNotPromoteThreatTruth ()

------------------------------------------------------------------------
-- 6. Weld to the existing formation / epistemic reopening owners.
------------------------------------------------------------------------

record ReligiousThreatBidiWeld : Set where
  constructor religious-threat-bidi-weld
  field
    formationBoundary : Formation.ChildReligiousAutonomyFormationBoundary
    reopeningBoundary : Reopening.ChildReligiousEpistemicReopeningBoundary
    claimBoundary : ClaimAudit.ReligiousPowerBidiBoundary
    pnfPatternSource : String
    dialecticPatternSource : String
    genericOwnersAreCanonicalOnPR650 : Bool
    adapterDoesNotClaimThoseOwnersMerged : Bool

open ReligiousThreatBidiWeld public

canonicalReligiousThreatBidiWeld : ReligiousThreatBidiWeld
canonicalReligiousThreatBidiWeld = religious-threat-bidi-weld
  Formation.canonicalChildReligiousAutonomyFormationBoundary
  Reopening.canonicalChildReligiousEpistemicReopeningBoundary
  ClaimAudit.canonicalReligiousPowerBidiBoundary
  "PR #650 DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact"
  "PR #650 DASHI.Reasoning.DialecticalOppositionNonExplosionExact"
  true true

------------------------------------------------------------------------
-- 7. Final predicate/dialectical no-collapse boundary.
------------------------------------------------------------------------

record ReligiousThreatPredicateDialecticBoundary : Set where
  constructor religious-threat-predicate-dialectic-boundary
  field
    naturalLanguageThreatIsAtomicClaim : Bool
    utteranceEstablishesMetaphysicalTruth : Bool
    utteranceEstablishesRecipientFear : Bool
    doctrinalCounterclaimEqualsLogicalNegation : Bool
    ethicalCounterpositionEqualsLogicalNegation : Bool
    authorityChallengeEqualsLogicalNegation : Bool
    crossContextDisagreementAutomaticallyContradicts : Bool
    unresolvedEqualsFalse : Bool
    threatRepresentationEqualsCoerciveEffect : Bool
    coerciveEffectEqualsEntrapment : Bool
    coerciveEffectEqualsLegalCoercion : Bool
    behaviourChangeEstablishesThreatTruth : Bool
    truthOfThreatEstablishesBehaviourChange : Bool
    authorityProvenanceRequiresIndependentReceipt : Bool
    recipientEffectRequiresIndependentReceipt : Bool
    exitAndBelongingPenaltyRequireIndependentReceipts : Bool

canonicalReligiousThreatPredicateDialecticBoundary :
  ReligiousThreatPredicateDialecticBoundary
canonicalReligiousThreatPredicateDialecticBoundary =
  religious-threat-predicate-dialectic-boundary
    false false false false false false false false false false false false false
    true true true
