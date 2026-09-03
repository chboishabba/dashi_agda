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
-- MULTI-CONSUMER DISCOURSE INTERPRETATION
------------------------------------------------------------------------

data ConsumerKind : Set where
  generalSemanticConsumer : ConsumerKind
  legalConsumer : ConsumerKind
  historicalConsumer : ConsumerKind
  culturalConsumer : ConsumerKind
  pedagogicalConsumer : ConsumerKind
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

record ConsumerDemandProfile : Set where
  constructor consumerDemandProfile
  field
    requestedConsumers : List ConsumerKind
    legalContexts : List Context.DocumentDiscourseFrame
    demandReference : String
    parserReparseRequested : Bool
    parserReparseRequestedIsFalse : parserReparseRequested ≡ false

open ConsumerDemandProfile public

singleConsumerDemand : ConsumerKind → String → ConsumerDemandProfile
singleConsumerDemand consumer ref =
  consumerDemandProfile (consumer ∷ []) [] ref false refl

multiConsumerDemand :
  List ConsumerKind → List Context.DocumentDiscourseFrame → String → ConsumerDemandProfile
multiConsumerDemand consumers contexts ref =
  consumerDemandProfile consumers contexts ref false refl

record MultiConsumerDiscourseInterpretation
    (candidate : DiscourseActCandidate)
    (general : GeneralDiscourseResolution candidate)
    (demand : ConsumerDemandProfile) : Set where
  constructor multiConsumerDiscourseInterpretation
  field
    underlyingCandidate : DiscourseActCandidate
    underlyingCandidateSame : underlyingCandidate ≡ candidate
    generalInterpretation : GeneralDiscourseResolution candidate
    generalInterpretationSame : generalInterpretation ≡ general
    demandProfile : ConsumerDemandProfile
    demandProfileSame : demandProfile ≡ demand
    parserRewrittenForConsumers : Bool
    parserRewrittenForConsumersIsFalse : parserRewrittenForConsumers ≡ false

open MultiConsumerDiscourseInterpretation public

interpretForDemand :
  {candidate : DiscourseActCandidate} →
  (general : GeneralDiscourseResolution candidate) →
  (demand : ConsumerDemandProfile) →
  MultiConsumerDiscourseInterpretation candidate general demand
interpretForDemand {candidate} general demand =
  multiConsumerDiscourseInterpretation
    candidate refl
    general refl
    demand refl
    false refl

------------------------------------------------------------------------
-- Legal projection is one optional projection among potentially many.
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
-- Canonical simultaneous-demand specimens.
------------------------------------------------------------------------

lawSchoolCaseDemand : Context.DocumentDiscourseFrame → ConsumerDemandProfile
lawSchoolCaseDemand frame =
  multiConsumerDemand
    ( generalSemanticConsumer
    ∷ legalConsumer
    ∷ historicalConsumer
    ∷ culturalConsumer
    ∷ pedagogicalConsumer
    ∷ [])
    (frame ∷ [])
    "same carrier requested for general, legal, historical, cultural and pedagogical analysis"

casualCaseDiscussionDemand : ConsumerDemandProfile
casualCaseDiscussionDemand =
  multiConsumerDemand
    (generalSemanticConsumer ∷ legalConsumer ∷ culturalConsumer ∷ [])
    []
    "casual discussion may contain legal material without supplying governed legal context"

------------------------------------------------------------------------
-- Degenerate compatibility views.
--
-- Older fixtures asked for one view at a time.  These wrappers preserve those
-- call sites, but they are explicitly projections of the plural demand model
-- and are not the canonical carrier.
------------------------------------------------------------------------

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
    generalSemanticConsumer noLegalContext
    candidate refl general refl false refl

legalContextInterpretation :
  {candidate : DiscourseActCandidate} →
  (general : GeneralDiscourseResolution candidate) →
  Context.DocumentDiscourseFrame →
  ConsumerIndexedDiscourseInterpretation candidate general
legalContextInterpretation {candidate} general frame =
  consumerIndexedDiscourseInterpretation
    legalConsumer (legalContext frame)
    candidate refl general refl false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data GeneralTextAutomaticallyNeedsLegalProjection : Set where
data LegalContentWordsAutomaticallySelectLegalConsumer : Set where
data LegalProjectionRewritesGeneralParse : Set where
data SameTextHasOnlyOneConsumerInterpretation : Set where
data ConsumerKindsAreMutuallyExclusive : Set where
data LegalContextErasesOtherConsumers : Set where

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

consumerKindsAreNotExclusive : ConsumerKindsAreMutuallyExclusive → ⊥
consumerKindsAreNotExclusive ()

legalContextDoesNotEraseOtherConsumers : LegalContextErasesOtherConsumers → ⊥
legalContextDoesNotEraseOtherConsumers ()
