module DASHI.Interop.TiRCorderHumourTlureyContextIndexedGrammarExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Interop.TiRCorderVoiceEditInteroceptionAntiPanopticonExact as Voice
import DASHI.Interop.TiRCorderSpokenIntentGrammarRuddCrossPollinationExact as Rudd
import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Reasoning.HumourRelationRepresentationCrossPollinationExact as HumourRR
import DASHI.Philosophy.RelationalProtocol as Tlurey

------------------------------------------------------------------------
-- TIRCORDER x HUMOUR x TLUREY CONTEXT-INDEXED EXTENSIBLE GRAMMAR
--
-- Cross-pollination only.  Brown/Pryce/Pabel's humour framework is not claimed
-- to be a speech-command theory, and Tlurey is not promoted into a universal
-- command semantics.  The useful structural overlap is:
--
--   Humour: meaning/adequacy is indexed by rationale, presenter, audience and
--           context, content, technical delivery, humour type and feedback.
--   Tlurey: direct action is only constructible after a witnessed
--           Respect -> Connect -> Reflect path.
--   Rudd/TiRCorder: recognized utterances map into candidate command fibres,
--                   with admission separated from execution.
--
-- Therefore an extensible grammar is not one global String -> Action table.
-- It is a context/consumer-indexed family whose registrations may exist before
-- they are admissible for execution in the current relation/context.
------------------------------------------------------------------------

data GrammarContextCoordinate : Set where
  rationaleCoordinate : GrammarContextCoordinate
  presenterCoordinate : GrammarContextCoordinate
  audienceContextCoordinate : GrammarContextCoordinate
  contentCoordinate : GrammarContextCoordinate
  deliveryCoordinate : GrammarContextCoordinate
  commandTypeCoordinate : GrammarContextCoordinate
  feedbackHistoryCoordinate : GrammarContextCoordinate

record GrammarContext : Set where
  constructor grammarContext
  field
    rationaleReference : String
    presenterReference : String
    audienceContextReference : String
    contentDomainReference : String
    deliveryModeReference : String
    commandTypeReference : String
    feedbackHistoryReference : String

open GrammarContext public

record ContextIndexedGrammarRule : Set where
  constructor contextIndexedGrammarRule
  field
    ruleReference : String
    utterancePatternReference : String
    baseRuleReference : String
    registrationContext : GrammarContext
    proposedFibre : Voice.SpokenIntentFibre
    proposedEditKind : Voice.VoiceEditKind
    sourceProvenanceReference : String

open ContextIndexedGrammarRule public

------------------------------------------------------------------------
-- Registration, contextual applicability, admission, and execution are four
-- distinct coordinates.
------------------------------------------------------------------------

data GrammarRegistrationStatus : Set where
  proposedRegistration : GrammarRegistrationStatus
  registeredRule : GrammarRegistrationStatus
  retiredRule : GrammarRegistrationStatus

record RegisteredGrammarRule : Set where
  constructor registeredGrammarRule
  field
    rule : ContextIndexedGrammarRule
    status : GrammarRegistrationStatus
    registrationReceiptReference : String

open RegisteredGrammarRule public

record ContextApplicabilityWitness : Set where
  constructor contextApplicabilityWitness
  field
    registeredRuleReference : String
    currentContext : GrammarContext
    satisfiedCoordinates : Nat
    unresolvedCoordinates : Nat
    applicabilityReceiptReference : String

open ContextApplicabilityWitness public

------------------------------------------------------------------------
-- Tlurey-shaped relational admission.  We deliberately reuse the existing
-- stage carriers: action is downstream of respect, connection and reflection.
------------------------------------------------------------------------

record GrammarRelationWitness : Set where
  constructor grammarRelationWitness
  field
    userReference : String
    grammarReference : String
    trustReference : String
    careReference : String
    sharedHistoryReference : String
    permissionToChallengeReference : String
    repairCommitmentReference : String
    recognitionReference : String

open GrammarRelationWitness public

record ReflectedGrammarContext : Set where
  constructor reflectedGrammarContext
  field
    relationWitness : GrammarRelationWitness
    respectedContextReference : String
    connectedContextReference : String
    reflectionReference : String
    applicability : ContextApplicabilityWitness

open ReflectedGrammarContext public

record DirectedGrammarExecution : Set where
  constructor directedGrammarExecution
  field
    reflectedContext : ReflectedGrammarContext
    admittedCandidateReference : String
    actionReference : String
    actionBoundaryReference : String

open DirectedGrammarExecution public

------------------------------------------------------------------------
-- Feedback changes future registration/context evidence; it does not rewrite
-- the historical utterance or silently redefine old command meaning.
------------------------------------------------------------------------

record GrammarFeedbackEvent : Set where
  constructor grammarFeedbackEvent
  field
    feedbackEventReference : String
    ruleReference : String
    contextReference : String
    observedOutcomeReference : String
    proposedRevisionReference : String

open GrammarFeedbackEvent public

data FeedbackRewritesHistoricalUtterance : Set where
feedbackDoesNotRewriteHistoricalUtterance : FeedbackRewritesHistoricalUtterance → ⊥
feedbackDoesNotRewriteHistoricalUtterance ()

data FeedbackAutomaticallyRewritesRule : Set where
feedbackDoesNotAutomaticallyRewriteRule : FeedbackAutomaticallyRewritesRule → ⊥
feedbackDoesNotAutomaticallyRewriteRule ()

------------------------------------------------------------------------
-- Wrong-consumer and overgeneralisation firewalls.
------------------------------------------------------------------------

data RegisteredEverywhereImpliesExecutableHere : Set where
registeredDoesNotImplyExecutableHere : RegisteredEverywhereImpliesExecutableHere → ⊥
registeredDoesNotImplyExecutableHere ()

data ExactPhraseMatchOverridesContext : Set where
exactPhraseMatchDoesNotOverrideContext : ExactPhraseMatchOverridesContext → ⊥
exactPhraseMatchDoesNotOverrideContext ()

data HumourContextDeterminesCommandMeaning : Set where
humourContextDoesNotDetermineCommandMeaning : HumourContextDeterminesCommandMeaning → ⊥
humourContextDoesNotDetermineCommandMeaning ()

data TlureyRelationDeterminesCommandTruth : Set where
tlureyRelationDoesNotDetermineCommandTruth : TlureyRelationDeterminesCommandTruth → ⊥
tlureyRelationDoesNotDetermineCommandTruth ()

data OneConsumerAdequacyImpliesPluralGrammarSafety : Set where
oneConsumerAdequacyDoesNotImplyPluralGrammarSafety : OneConsumerAdequacyImpliesPluralGrammarSafety → ⊥
oneConsumerAdequacyDoesNotImplyPluralGrammarSafety ()

------------------------------------------------------------------------
-- Source/owner anchors.  These establish reuse, not semantic identity.
------------------------------------------------------------------------

humourSourceAnchor : Humour.HumourFrameworkSourceSurface
humourSourceAnchor = Humour.canonicalHumourFrameworkSourceSurface

humourConsumerSafetyAnchor : HumourRR.HumourRelationRepresentationBoundary
humourConsumerSafetyAnchor = HumourRR.canonicalHumourRelationRepresentationBoundary

voiceBoundaryAnchor : Voice.TiRCorderVoiceEditInteroceptionBoundary
voiceBoundaryAnchor = Voice.canonicalTiRCorderVoiceEditInteroceptionBoundary

ruddGrammarBoundaryAnchor : Rudd.SpokenIntentInterpreterBoundary
ruddGrammarBoundaryAnchor = Rudd.canonicalSpokenIntentInterpreterBoundary

------------------------------------------------------------------------
-- Canonical integration boundary.
------------------------------------------------------------------------

record ContextIndexedGrammarBoundary : Set where
  constructor contextIndexedGrammarBoundary
  field
    grammarIsGlobalUnindexedStringToActionMap : Bool
    registeredRuleAutomaticallyExecutes : Bool
    exactMatchOverridesAudienceAndContext : Bool
    feedbackAutomaticallyChangesRuleMeaning : Bool
    actionRequiresReflectedContext : Bool
    provenanceSurvivesGrammarExtension : Bool
    pluralConsumerSafetyRequiresSeparateChecks : Bool
    verbatimCarrierRemainsPriorToGrammarAction : Bool

canonicalContextIndexedGrammarBoundary : ContextIndexedGrammarBoundary
canonicalContextIndexedGrammarBoundary =
  contextIndexedGrammarBoundary
    false
    false
    false
    false
    true
    true
    true
    true
