module DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context

------------------------------------------------------------------------
-- CONSUMER-INDEXED DISCOURSE INTERPRETATION
--
-- SensibLaw parses general text first.  Legal interpretation is an optional
-- consumer/context projection over the same underlying semantic carrier; it is
-- never a parser mode that rewrites ordinary text into legal terminology.
------------------------------------------------------------------------

data ConsumerKind : Set where
  generalSemanticConsumer : ConsumerKind
  legalConsumer : ConsumerKind
  historicalConsumer : ConsumerKind
  culturalConsumer : ConsumerKind
  customConsumer : String → ConsumerKind

data GeneralDiscourseKind : Set where
  assertionDiscourse
  reportDiscourse
  quotationDiscourse
  denialDiscourse
  testimonyDiscourse
  questionDiscourse
  hypotheticalDiscourse
  unresolvedDiscourse
  : GeneralDiscourseKind

record DiscourseActCandidate : Set where
  constructor discourseActCandidate
  field
    governorCandidate : Candidate.CandidateSemanticFragment
    sourceCandidate : Candidate.CandidateSemanticFragment
    contentCandidate : Candidate.CandidateSemanticFragment
    sourceReference : String
    contentReference : String
    contextEvidenceReferences : List String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open DiscourseActCandidate public

record GeneralDiscourseResolution (candidate : DiscourseActCandidate) : Set where
  constructor generalDiscourseResolution
  field
    discourseKind : GeneralDiscourseKind
    propositionStatus : Status.PropositionStatus
    occurrenceStatus : Status.OccurrenceStatus
    truthStatus : Status.TruthStatus
    attribution : Status.AttributionRole
    resolverReference : String
    legalVocabularyRequired : Bool
    legalVocabularyRequiredIsFalse : legalVocabularyRequired ≡ false

open GeneralDiscourseResolution public

data OptionalLegalContext : Set where
  noLegalContext : OptionalLegalContext
  legalContext : Context.DocumentDiscourseFrame → OptionalLegalContext

record ConsumerIndexedDiscourseInterpretation
    (candidate : DiscourseActCandidate)
    (general : GeneralDiscourseResolution candidate) : Set where
  constructor consumerIndexedDiscourseInterpretation
  field
    consumer : ConsumerKind
    legalContextSelection : OptionalLegalContext
    underlyingCandidate : DiscourseActCandidate
    underlyingCandidateSame : underlyingCandidate ≡ candidate
    generalInterpretation : GeneralDiscourseResolution candidate
    generalInterpretationSame : generalInterpretation ≡ general
    parserRewrittenForConsumer : Bool
    parserRewrittenForConsumerIsFalse : parserRewrittenForConsumer ≡ false

open ConsumerIndexedDiscourseInterpretation public

generalOnlyInterpretation :
  {candidate : DiscourseActCandidate} →
  (general : GeneralDiscourseResolution candidate) →
  ConsumerIndexedDiscourseInterpretation candidate general
generalOnlyInterpretation {candidate} general =
  consumerIndexedDiscourseInterpretation
    generalSemanticConsumer
    noLegalContext
    candidate refl
    general refl
    false refl

legalContextInterpretation :
  {candidate : DiscourseActCandidate} →
  (general : GeneralDiscourseResolution candidate) →
  Context.DocumentDiscourseFrame →
  ConsumerIndexedDiscourseInterpretation candidate general
legalContextInterpretation {candidate} general frame =
  consumerIndexedDiscourseInterpretation
    legalConsumer
    (legalContext frame)
    candidate refl
    general refl
    false refl

------------------------------------------------------------------------
-- A legal projection is separately constructed from a legal-context frame.
-- The same general proposition may be used with or without this projection.
------------------------------------------------------------------------

record LegalDiscourseProjection
    {candidate : DiscourseActCandidate}
    (general : GeneralDiscourseResolution candidate)
    (frame : Context.DocumentDiscourseFrame) : Set where
  constructor legalDiscourseProjection
  field
    generalStatus : Status.PropositionStatus
    generalStatusPreserved : generalStatus ≡ propositionStatus general
    legalPropositionStatus : Status.PropositionStatus
    legalJudicialStatus : Status.JudicialDiscourseStatus
    legalAttribution : Status.AttributionRole
    truthStatusPreserved : Status.TruthStatus
    truthStatusPreservedExact : truthStatusPreserved ≡ truthStatus general
    legalContextReference : String

open LegalDiscourseProjection public

projectLegalDiscourse :
  {candidate : DiscourseActCandidate} →
  (general : GeneralDiscourseResolution candidate) →
  (frame : Context.DocumentDiscourseFrame) →
  LegalDiscourseProjection general frame
projectLegalDiscourse general frame =
  legalDiscourseProjection
    (propositionStatus general) refl
    (Context.rolePropositionStatus (Context.role frame))
    (Context.roleJudicialStatus (Context.role frame))
    (Context.roleAttribution (Context.role frame))
    (truthStatus general) refl
    (Context.regionReference frame)

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data GeneralTextAutomaticallyNeedsLegalProjection : Set where
data LegalContentWordsAutomaticallySelectLegalConsumer : Set where
data LegalProjectionRewritesGeneralParse : Set where
data SameTextHasOnlyOneConsumerInterpretation : Set where

generalTextDoesNotAutomaticallyNeedLegalProjection :
  GeneralTextAutomaticallyNeedsLegalProjection → ⊥
generalTextDoesNotAutomaticallyNeedLegalProjection ()

legalWordsDoNotAutomaticallySelectLegalConsumer :
  LegalContentWordsAutomaticallySelectLegalConsumer → ⊥
legalWordsDoNotAutomaticallySelectLegalConsumer ()

legalProjectionDoesNotRewriteGeneralParse :
  LegalProjectionRewritesGeneralParse → ⊥
legalProjectionDoesNotRewriteGeneralParse ()

sameTextMayHaveSeveralConsumerInterpretations :
  SameTextHasOnlyOneConsumerInterpretation → ⊥
sameTextMayHaveSeveralConsumerInterpretations ()
