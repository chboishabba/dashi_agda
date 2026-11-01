module DASHI.Law.WaltonsEstoppelOperationalPipelineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC
import DASHI.Law.SensibLawOALCJudgmentCitationSnowballExact as Judgment
import DASHI.Law.WaltonsReviewedPropositionPaymentExact as Review
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawRuntimeWrongTypeElementFrontierExact as WrongType

------------------------------------------------------------------------
-- WALTONS / ESTOPPEL OPERATIONAL PIPELINE
--
-- This module owns the executable stage structure, not the legal conclusions.
-- Machine transitions may acquire, materialise, queue, compile and aggregate.
-- Explicit human/legal review remains required before proposition-evidence
-- payment and before citation-use/treatment edges enter the genealogy.
------------------------------------------------------------------------

data WaltonsPipelineStage : Set where
  acquireWaltonsPrimarySource : WaltonsPipelineStage
  materialiseWaltonsReviewQueue : WaltonsPipelineStage
  reviewWaltonsParagraphs : WaltonsPipelineStage
  compileWaltonsReviewedReceipts : WaltonsPipelineStage
  inspectWaltonsWrongTypeFrontier : WaltonsPipelineStage
  discoverLaterTreatmentCitedBy : WaltonsPipelineStage
  reviewLaterTreatmentPropositions : WaltonsPipelineStage
  buildTemporalTreatmentGenealogy : WaltonsPipelineStage

data StageExecutionClass : Set where
  machineExecutable : StageExecutionClass
  humanLegalReviewRequired : StageExecutionClass
  externalProviderRequired : StageExecutionClass

executionClass : WaltonsPipelineStage → StageExecutionClass
executionClass acquireWaltonsPrimarySource = machineExecutable
executionClass materialiseWaltonsReviewQueue = machineExecutable
executionClass reviewWaltonsParagraphs = humanLegalReviewRequired
executionClass compileWaltonsReviewedReceipts = machineExecutable
executionClass inspectWaltonsWrongTypeFrontier = machineExecutable
executionClass discoverLaterTreatmentCitedBy = externalProviderRequired
executionClass reviewLaterTreatmentPropositions = humanLegalReviewRequired
executionClass buildTemporalTreatmentGenealogy = machineExecutable

reviewWaltonsIsHumanGate :
  executionClass reviewWaltonsParagraphs ≡ humanLegalReviewRequired
reviewWaltonsIsHumanGate = refl

reviewTreatmentIsHumanGate :
  executionClass reviewLaterTreatmentPropositions ≡ humanLegalReviewRequired
reviewTreatmentIsHumanGate = refl

citedByIsExternalProviderGate :
  executionClass discoverLaterTreatmentCitedBy ≡ externalProviderRequired
citedByIsExternalProviderGate = refl

data StageArtifact : WaltonsPipelineStage → Set where
  waltonsPinnedOalcReceipt :
    StageArtifact acquireWaltonsPrimarySource
  waltonsCandidateReviewQueue :
    StageArtifact materialiseWaltonsReviewQueue
  waltonsReviewerDecisionFile :
    StageArtifact reviewWaltonsParagraphs
  waltonsReviewedEvidenceReceipts :
    StageArtifact compileWaltonsReviewedReceipts
  waltonsWrongTypeFrontier :
    StageArtifact inspectWaltonsWrongTypeFrontier
  waltonsCitedByCandidateManifest :
    StageArtifact discoverLaterTreatmentCitedBy
  laterAuthorityReviewedTreatmentReceipts :
    StageArtifact reviewLaterTreatmentPropositions
  waltonsTemporalTreatmentGenealogy :
    StageArtifact buildTemporalTreatmentGenealogy

------------------------------------------------------------------------
-- Existing owners anchor each critical semantic boundary.
------------------------------------------------------------------------

OalcBoundary : Set
OalcBoundary = OALC.OalcLegalFollowAttributionBoundary

oalcBoundaryPaid : OalcBoundary
oalcBoundaryPaid = OALC.canonicalOalcLegalFollowAttributionBoundary

JudgmentBoundary : Set
JudgmentBoundary = Judgment.OalcJudgmentCitationSnowballBoundary

judgmentBoundaryPaid : JudgmentBoundary
judgmentBoundaryPaid = Judgment.canonicalOalcJudgmentCitationSnowballBoundary

ReviewedPaymentBoundary : Set
ReviewedPaymentBoundary = Review.WaltonsReviewedPropositionPaymentBoundary

reviewedPaymentBoundaryPaid : ReviewedPaymentBoundary
reviewedPaymentBoundaryPaid = Review.canonicalWaltonsReviewedPropositionPaymentBoundary

WrongTypeBoundary : Set
WrongTypeBoundary = WrongType.RuntimeWrongTypeElementBoundary

wrongTypeBoundaryPaid : WrongTypeBoundary
wrongTypeBoundaryPaid = WrongType.canonicalRuntimeWrongTypeElementBoundary

waltonsCitedByTraversal : Query.CitationTraversal
waltonsCitedByTraversal = Query.jadeCitedByTraversal "[1988] HCA 7"

------------------------------------------------------------------------
-- No-collapse laws for orchestration.
------------------------------------------------------------------------

data ReviewWorksheetAutomaticallyDecision : Set where
data CitedByProviderHitAutomaticallyTreatment : Set where
data OalcReacquisitionAutomaticallyTreatment : Set where
data WrongTypeSatisfiedAutomaticallyCurrentLaw : Set where
data TreatmentGenealogyAutomaticallyCurrentLaw : Set where
data MissingProviderMayBeReplacedByTextSearch : Set where
data PipelineCompletionCreatesLegalAuthority : Set where

worksheetDoesNotCreateDecision :
  ReviewWorksheetAutomaticallyDecision → ⊥
worksheetDoesNotCreateDecision ()

citedByHitDoesNotCreateTreatment :
  CitedByProviderHitAutomaticallyTreatment → ⊥
citedByHitDoesNotCreateTreatment ()

oalcReacquisitionDoesNotCreateTreatment :
  OalcReacquisitionAutomaticallyTreatment → ⊥
oalcReacquisitionDoesNotCreateTreatment ()

wrongTypeSatisfiedDoesNotCreateCurrentLaw :
  WrongTypeSatisfiedAutomaticallyCurrentLaw → ⊥
wrongTypeSatisfiedDoesNotCreateCurrentLaw ()

genealogyDoesNotCreateCurrentLaw :
  TreatmentGenealogyAutomaticallyCurrentLaw → ⊥
genealogyDoesNotCreateCurrentLaw ()

textSearchCannotSubstituteForCitedBy :
  MissingProviderMayBeReplacedByTextSearch → ⊥
textSearchCannotSubstituteForCitedBy ()

pipelineCompletionDoesNotCreateAuthority :
  PipelineCompletionCreatesLegalAuthority → ⊥
pipelineCompletionDoesNotCreateAuthority ()

record WaltonsOperationalPipelineBoundary : Set where
  constructor waltonsOperationalPipelineBoundary
  field
    eightStagesExplicit : Bool
    eightStagesExplicitIsTrue : eightStagesExplicit ≡ true

    paragraphReviewHumanGated : Bool
    paragraphReviewHumanGatedIsTrue : paragraphReviewHumanGated ≡ true

    treatmentReviewHumanGated : Bool
    treatmentReviewHumanGatedIsTrue : treatmentReviewHumanGated ≡ true

    citedByProviderExplicit : Bool
    citedByProviderExplicitIsTrue : citedByProviderExplicit ≡ true

    citedByMayDegradeToTextSearch : Bool
    citedByMayDegradeToTextSearchIsFalse :
      citedByMayDegradeToTextSearch ≡ false

    laterAuthoritiesReacquiredAsPrimarySources : Bool
    laterAuthoritiesReacquiredAsPrimarySourcesIsTrue :
      laterAuthoritiesReacquiredAsPrimarySources ≡ true

    genealogyUsesReviewedTreatmentOnly : Bool
    genealogyUsesReviewedTreatmentOnlyIsTrue :
      genealogyUsesReviewedTreatmentOnly ≡ true

    pipelineCreatesLegalAuthority : Bool
    pipelineCreatesLegalAuthorityIsFalse :
      pipelineCreatesLegalAuthority ≡ false

canonicalWaltonsOperationalPipelineBoundary :
  WaltonsOperationalPipelineBoundary
canonicalWaltonsOperationalPipelineBoundary =
  waltonsOperationalPipelineBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
