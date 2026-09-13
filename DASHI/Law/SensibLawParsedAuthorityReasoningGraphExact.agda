module DASHI.Law.SensibLawParsedAuthorityReasoningGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawCitationUsePropositionExact as Citation

------------------------------------------------------------------------
-- PARSED AUTHORITY REASONING GRAPH
--
-- Each newly parsed judgment can enrich the reusable legal graph with more
-- than document-level citation topology: proposition use, treatment, facts,
-- conditions/circumstances, reasoning role, outcome and lexical realisation.
------------------------------------------------------------------------

data ReasoningRole : Set where
  premiseRole
  ruleRole
  exceptionRole
  analogyRole
  distinctionRole
  policyRole
  factualFindingRole
  burdenRole
  remedyRole
  reasoningRoleUnresolved
  : ReasoningRole

data ConditionKind : Set where
  factualCondition
  legalCondition
  jurisdictionCondition
  temporalCondition
  proceduralCondition
  evidentialCondition
  exceptionCondition
  conditionUnresolved
  : ConditionKind

record ConditionCoordinate : Set where
  constructor conditionCoordinate
  field
    conditionReference : String
    kind : ConditionKind
    propositionReference : String
    sourceSpanReference : String
    reviewReference : String

open ConditionCoordinate public

data OutcomeKind : Set where
  applicantSuccess
  respondentSuccess
  mixedOutcome
  remittedOutcome
  dismissedOutcome
  outcomeUnresolved
  : OutcomeKind

record ParsedAuthorityReasoningDelta : Set₁ where
  constructor parsedAuthorityReasoningDelta
  field
    documentReference : String
    caseReference : String
    courtReference : String
    judgeOrSpeakerReference : String
    jurisdictionReference : String
    temporalReference : String
    citingPropositionReference : String
    citedPropositionReference : String
    citationUse : Citation.PropositionCitationUse
    conditionsAndCircumstances : List ConditionCoordinate
    reasoningRole : ReasoningRole
    outcome : OutcomeKind
    exceptionReferences : List String
    burdenReferences : List String
    remedyReferences : List String
    lexicalRealisationReferences : List String
    directTextSupportReceipt : Set
    reviewedReasoningReceipt : Set
    deltaReference : String

open ParsedAuthorityReasoningDelta public

record PropositionReasoningEdge : Set₁ where
  constructor propositionReasoningEdge
  field
    sourcePropositionReference : String
    targetPropositionReference : String
    citationUse : Citation.PropositionCitationUse
    reasoningRole : ReasoningRole
    conditions : List ConditionCoordinate
    outcome : OutcomeKind
    edgeReference : String

open PropositionReasoningEdge public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CitationTreatmentMeansHolding : Set where
data ConditionCooccurrenceMeansApplicability : Set where
data ReasoningRoleCandidateMeansRatio : Set where
data OutcomeCorrelationMeansDoctrinalCause : Set where
data LexicalRealisationMeansSemanticIdentity : Set where

citationTreatmentDoesNotMeanHolding : CitationTreatmentMeansHolding → ⊥
citationTreatmentDoesNotMeanHolding ()

conditionCooccurrenceDoesNotMeanApplicability :
  ConditionCooccurrenceMeansApplicability → ⊥
conditionCooccurrenceDoesNotMeanApplicability ()

reasoningRoleDoesNotMeanRatio : ReasoningRoleCandidateMeansRatio → ⊥
reasoningRoleDoesNotMeanRatio ()

outcomeCorrelationDoesNotMeanDoctrinalCause :
  OutcomeCorrelationMeansDoctrinalCause → ⊥
outcomeCorrelationDoesNotMeanDoctrinalCause ()

lexicalRealisationDoesNotMeanSemanticIdentity :
  LexicalRealisationMeansSemanticIdentity → ⊥
lexicalRealisationDoesNotMeanSemanticIdentity ()

record ParsedAuthorityReasoningBoundary : Set where
  constructor parsedAuthorityReasoningBoundary
  field
    graphIsPropositionLevel : Bool
    graphIsPropositionLevelIsTrue : graphIsPropositionLevel ≡ true
    conditionsAndCircumstancesRetained : Bool
    conditionsAndCircumstancesRetainedIsTrue : conditionsAndCircumstancesRetained ≡ true
    reasoningRoleRetained : Bool
    reasoningRoleRetainedIsTrue : reasoningRoleRetained ≡ true
    outcomeAndTreatmentRemainDistinct : Bool
    outcomeAndTreatmentRemainDistinctIsTrue : outcomeAndTreatmentRemainDistinct ≡ true
    parsedGraphDeltaEqualsHolding : Bool
    parsedGraphDeltaEqualsHoldingIsFalse : parsedGraphDeltaEqualsHolding ≡ false

canonicalParsedAuthorityReasoningBoundary : ParsedAuthorityReasoningBoundary
canonicalParsedAuthorityReasoningBoundary =
  parsedAuthorityReasoningBoundary true refl true refl true refl true refl false refl
