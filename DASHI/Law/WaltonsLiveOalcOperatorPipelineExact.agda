module DASHI.Law.WaltonsLiveOalcOperatorPipelineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianContractsReviewedHopCompilerExact as Reviewed
import DASHI.Law.AustralianContractsLandscapeControllerExact as Landscape
import DASHI.Law.SensibLawNativeLegalFollowCLIExact as CLI

------------------------------------------------------------------------
-- LIVE WALTONS / OALC OPERATOR PIPELINE
--
-- Every deterministic step is native Rust.  The pipeline stops only where an
-- external provider or a human legal review is genuinely required.
------------------------------------------------------------------------

data LiveOperatorGate : Set where
  humanParagraphReview : LiveOperatorGate
  externalCitedByProvider : LiveOperatorGate
  humanAuthorityIdentityReview : LiveOperatorGate
  humanTreatmentReview : LiveOperatorGate
  noOperatorGate : LiveOperatorGate

data LivePipelineStage : Set where
  sourcePrepared : LivePipelineStage
  paragraphReviewed : LivePipelineStage
  citedByReacquired : LivePipelineStage
  authorityIdentityReviewed : LivePipelineStage
  treatmentReviewed : LivePipelineStage
  livePipelineComplete : LivePipelineStage

liveGateOrder : List LiveOperatorGate
liveGateOrder =
  humanParagraphReview
    ∷ externalCitedByProvider
    ∷ humanAuthorityIdentityReview
    ∷ humanTreatmentReview
    ∷ noOperatorGate
    ∷ []

record WaltonsLiveOalcPipelineBoundary : Set where
  constructor waltonsLiveOalcPipelineBoundary
  field
    liveOalcAcquisitionIsNativeRust : Bool
    liveOalcAcquisitionIsNativeRustIsTrue :
      liveOalcAcquisitionIsNativeRust ≡ true

    paragraphReviewIsAutomatic : Bool
    paragraphReviewIsAutomaticIsFalse :
      paragraphReviewIsAutomatic ≡ false

    paragraphReviewRequiresExplicitCompletion : Bool
    paragraphReviewRequiresExplicitCompletionIsTrue :
      paragraphReviewRequiresExplicitCompletion ≡ true

    citedByProviderResultCreatesTreatment : Bool
    citedByProviderResultCreatesTreatmentIsFalse :
      citedByProviderResultCreatesTreatment ≡ false

    laterAuthoritiesAreReacquiredThroughOalc : Bool
    laterAuthoritiesAreReacquiredThroughOalcIsTrue :
      laterAuthoritiesAreReacquiredThroughOalc ≡ true

    rawOalcIdentityCreatesCanonicalAlias : Bool
    rawOalcIdentityCreatesCanonicalAliasIsFalse :
      rawOalcIdentityCreatesCanonicalAlias ≡ false

    authorityIdentityRequiresReview : Bool
    authorityIdentityRequiresReviewIsTrue :
      authorityIdentityRequiresReview ≡ true

    authorityIdentityReviewRequiresExplicitCompletion : Bool
    authorityIdentityReviewRequiresExplicitCompletionIsTrue :
      authorityIdentityReviewRequiresExplicitCompletion ≡ true

    citationOccurrenceCreatesTreatment : Bool
    citationOccurrenceCreatesTreatmentIsFalse :
      citationOccurrenceCreatesTreatment ≡ false

    treatmentRequiresReview : Bool
    treatmentRequiresReviewIsTrue :
      treatmentRequiresReview ≡ true

    treatmentReviewRequiresExplicitCompletion : Bool
    treatmentReviewRequiresExplicitCompletionIsTrue :
      treatmentReviewRequiresExplicitCompletion ≡ true

    deterministicStagesResumeWithoutSemanticJson : Bool
    deterministicStagesResumeWithoutSemanticJsonIsTrue :
      deterministicStagesResumeWithoutSemanticJson ≡ true

    finalTrajectoryUsesTypedS14Sync : Bool
    finalTrajectoryUsesTypedS14SyncIsTrue :
      finalTrajectoryUsesTypedS14Sync ≡ true

    pipelineCreatesLegalAuthority : Bool
    pipelineCreatesLegalAuthorityIsFalse :
      pipelineCreatesLegalAuthority ≡ false

    pipelineCreatesCurrentLawConclusion : Bool
    pipelineCreatesCurrentLawConclusionIsFalse :
      pipelineCreatesCurrentLawConclusion ≡ false

open WaltonsLiveOalcPipelineBoundary public

canonicalWaltonsLiveOalcPipelineBoundary : WaltonsLiveOalcPipelineBoundary
canonicalWaltonsLiveOalcPipelineBoundary =
  waltonsLiveOalcPipelineBoundary
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

data ExternalCitedByAutomaticallyTreatment : Set where
data RawOalcIdentityAutomaticallyAlias : Set where
data CitationOccurrenceAutomaticallyTreatment : Set where
data LivePipelineAutomaticallyLegalAuthority : Set where
data LivePipelineAutomaticallyCurrentLaw : Set where

externalCitedByDoesNotCreateTreatment :
  ExternalCitedByAutomaticallyTreatment → ⊥
externalCitedByDoesNotCreateTreatment ()

rawOalcIdentityDoesNotCreateAlias :
  RawOalcIdentityAutomaticallyAlias → ⊥
rawOalcIdentityDoesNotCreateAlias ()

citationOccurrenceDoesNotCreateTreatment :
  CitationOccurrenceAutomaticallyTreatment → ⊥
citationOccurrenceDoesNotCreateTreatment ()

livePipelineDoesNotCreateAuthority :
  LivePipelineAutomaticallyLegalAuthority → ⊥
livePipelineDoesNotCreateAuthority ()

livePipelineDoesNotCreateCurrentLaw :
  LivePipelineAutomaticallyCurrentLaw → ⊥
livePipelineDoesNotCreateCurrentLaw ()

ReviewedBoundary : Set
ReviewedBoundary = Reviewed.AustralianContractsReviewedHopCompilerBoundary

reviewedBoundaryPaid : ReviewedBoundary
reviewedBoundaryPaid = Reviewed.canonicalAustralianContractsReviewedHopCompilerBoundary

LandscapeBoundary : Set
LandscapeBoundary = Landscape.AustralianContractsLandscapeControllerBoundary

landscapeBoundaryPaid : LandscapeBoundary
landscapeBoundaryPaid = Landscape.canonicalAustralianContractsLandscapeControllerBoundary

CliBoundary : Set
CliBoundary = CLI.NativeLegalFollowCliBoundary

cliBoundaryPaid : CliBoundary
cliBoundaryPaid = CLI.canonicalNativeLegalFollowCliBoundary
