module DASHI.Cognition.PNF.SensibLawLegalOutcomeIdentifiabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- Cross-pollinated from InverseProblemIdentifiabilityBidiExact and #705
-- partial-identification work: an observed legal disposition is an observable,
-- not the latent doctrinal/procedural explanation.
------------------------------------------------------------------------

data DispositionSurface : Set where
  allowed dismissed refused granted remitted stayed unresolvedDisposition : DispositionSurface

data LegalExplanationKind : Set where
  meritsExplanation
  jurisdictionExplanation
  limitationExplanation
  evidenceFailureExplanation
  proceduralDefaultExplanation
  discretionExplanation
  constitutionalExplanation
  settlementOrConsentExplanation
  explanationUnresolved
  : LegalExplanationKind

record LegalOutcomeModel : Set₁ where
  constructor legalOutcomeModel
  field
    LegalState : Set
    explanation : LegalState → LegalExplanationKind
    disposition : LegalState → DispositionSurface
    modelReference : String

open LegalOutcomeModel public

record OutcomeDegeneracyWitness (model : LegalOutcomeModel) : Set where
  constructor outcomeDegeneracyWitness
  field
    left right : LegalState model
    sameDisposition : disposition model left ≡ disposition model right
    differentExplanation : explanation model left ≢ explanation model right
    witnessReference : String

open OutcomeDegeneracyWitness public

record GloballyOutcomeIdentifiable (model : LegalOutcomeModel) : Set where
  constructor globallyOutcomeIdentifiable
  field
    dispositionSeparates :
      (x y : LegalState model) →
      disposition model x ≡ disposition model y →
      x ≡ y

open GloballyOutcomeIdentifiable public

outcomeDegeneracyRefutesGlobalIdentifiability :
  (model : LegalOutcomeModel) →
  OutcomeDegeneracyWitness model →
  GloballyOutcomeIdentifiable model →
  ⊥
outcomeDegeneracyRefutesGlobalIdentifiability model witness identifiable =
  differentExplanation witness
    (cong (explanation model)
      (dispositionSeparates identifiable
        (left witness)
        (right witness)
        (sameDisposition witness)))

------------------------------------------------------------------------
-- Partial explanation fibre: preserve all currently compatible explanations.
------------------------------------------------------------------------

record ExplanationCandidate : Set where
  constructor explanationCandidate
  field
    kind : LegalExplanationKind
    sourceReference : String
    candidateOnly : Bool

open ExplanationCandidate public

record OutcomeExplanationFibre : Set where
  constructor outcomeExplanationFibre
  field
    observedDisposition : DispositionSurface
    candidates : List ExplanationCandidate
    sourceRecordReference : String
    exactReasonResolved : Bool
    fibreReference : String

open OutcomeExplanationFibre public

data ExplanationResidual : Set where
  sourceReasonResidual
  proceduralHistoryResidual
  jurisdictionResidual
  reasonsForJudgmentResidual
  exactExplanationClosed
  : ExplanationResidual

data ExplanationProducer : Set where
  inspectDispositionSource
  inspectProceduralHistory
  inspectJurisdictionRecord
  inspectReasonsForJudgment
  : ExplanationProducer

producerForExplanationResidual : ExplanationResidual → ExplanationProducer
producerForExplanationResidual sourceReasonResidual = inspectDispositionSource
producerForExplanationResidual proceduralHistoryResidual = inspectProceduralHistory
producerForExplanationResidual jurisdictionResidual = inspectJurisdictionRecord
producerForExplanationResidual reasonsForJudgmentResidual = inspectReasonsForJudgment
producerForExplanationResidual exactExplanationClosed = inspectDispositionSource

record ExplanationCutset : Set where
  constructor explanationCutset
  field
    sourceReasonClosed : Bool
    proceduralHistoryClosed : Bool
    jurisdictionClosed : Bool
    reasonsForJudgmentClosed : Bool
    cutsetReference : String

open ExplanationCutset public

firstExplanationResidual : ExplanationCutset → ExplanationResidual
firstExplanationResidual c with sourceReasonClosed c
... | false = sourceReasonResidual
... | true with proceduralHistoryClosed c
...   | false = proceduralHistoryResidual
...   | true with jurisdictionClosed c
...     | false = jurisdictionResidual
...     | true with reasonsForJudgmentClosed c
...       | false = reasonsForJudgmentResidual
...       | true = exactExplanationClosed

------------------------------------------------------------------------
-- Consumer-relative closure: a consumer may only need the candidate fibre,
-- while another demands exact reasons.
------------------------------------------------------------------------

data ExplanationConsumerGoal : Set where
  listCompatibleExplanations exactDispositionReason : ExplanationConsumerGoal

data ExplanationGoalStatus : Set where explanationGoalClosed explanationGoalOpen : ExplanationGoalStatus

goalStatus : ExplanationConsumerGoal → OutcomeExplanationFibre → ExplanationGoalStatus
goalStatus listCompatibleExplanations fibre = explanationGoalClosed
goalStatus exactDispositionReason fibre with exactReasonResolved fibre
... | true = explanationGoalClosed
... | false = explanationGoalOpen

canonicalAmbiguousDisposition : OutcomeExplanationFibre
canonicalAmbiguousDisposition =
  outcomeExplanationFibre dismissed
    ( explanationCandidate jurisdictionExplanation "candidate jurisdictional basis" true
    ∷ explanationCandidate proceduralDefaultExplanation "candidate procedural basis" true
    ∷ explanationCandidate meritsExplanation "candidate merits basis" true
    ∷ [])
    "terse dismissal surface without verified reasons"
    false
    "three compatible explanation candidates retained"

candidateListCanCloseWithoutExactReason :
  goalStatus listCompatibleExplanations canonicalAmbiguousDisposition ≡ explanationGoalClosed
candidateListCanCloseWithoutExactReason = refl

exactReasonRemainsOpen :
  goalStatus exactDispositionReason canonicalAmbiguousDisposition ≡ explanationGoalOpen
exactReasonRemainsOpen = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data DispositionSurfaceUniquelyDeterminesReason : Set where
data CandidateExplanationIsAuthoritativeReason : Set where
data ConsumerCandidateClosureMeansExactIdentification : Set where

dispositionDoesNotUniquelyDetermineReason : DispositionSurfaceUniquelyDeterminesReason → ⊥
dispositionDoesNotUniquelyDetermineReason ()
candidateExplanationIsNotAuthoritativeReason : CandidateExplanationIsAuthoritativeReason → ⊥
candidateExplanationIsNotAuthoritativeReason ()
candidateClosureDoesNotMeanExactIdentification : ConsumerCandidateClosureMeansExactIdentification → ⊥
candidateClosureDoesNotMeanExactIdentification ()

record LegalOutcomeIdentifiabilityBoundary : Set where
  constructor legal-outcome-identifiability-boundary
  field
    observedDispositionIsLatentLegalState : Bool
    sameDispositionImpliesSameExplanation : Bool
    compatibleExplanationListMayCloseForCoarseConsumer : Bool
    exactReasonRequiresAdditionalProducer : Bool

canonicalLegalOutcomeIdentifiabilityBoundary : LegalOutcomeIdentifiabilityBoundary
canonicalLegalOutcomeIdentifiabilityBoundary =
  legal-outcome-identifiability-boundary false false true true
