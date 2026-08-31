module DASHI.Core.ExternalAutoformalizationProvenanceExact where

open import Agda.Builtin.Equality using (_≡_)

-- Generic provenance boundary motivated by the 2026 wave of LLM-assisted
-- mathematics and autoformalization.  This module is domain-neutral.

data FormalizationStage : Set where
  informalMathematics : FormalizationStage
  llmGeneratedFormalText : FormalizationStage
  proofAssistantParsed : FormalizationStage
  kernelAccepted : FormalizationStage
  statementCorrespondenceReviewed : FormalizationStage
  humanMathematicalReview : FormalizationStage
  independentlyReproduced : FormalizationStage

data ContributionKind : Set where
  newMathematicalIdea : ContributionKind
  proofCompletion : ContributionKind
  formalTranslation : ContributionKind
  librarySearch : ContributionKind
  proofRepair : ContributionKind
  verificationOnly : ContributionKind
  mixedOrUnresolved : ContributionKind

record FormalizationProvenance : Set where
  field
    sourceStage : FormalizationStage
    targetStage : FormalizationStage
    contribution : ContributionKind
    modelIdentityRecorded : Set
    promptOrInteractionRecord : Set
    dependencyRecord : Set
    humanReviewRecord : Set

kernelAcceptanceNotHumanReview : kernelAccepted ≡ humanMathematicalReview -> ⊥
kernelAcceptanceNotHumanReview ()

formalTextNotKernelAcceptance : llmGeneratedFormalText ≡ kernelAccepted -> ⊥
formalTextNotKernelAcceptance ()

correspondenceNotIndependentReproduction : statementCorrespondenceReviewed ≡ independentlyReproduced -> ⊥
correspondenceNotIndependentReproduction ()

formalTranslationNotNewIdea : formalTranslation ≡ newMathematicalIdea -> ⊥
formalTranslationNotNewIdea ()

record PromotionReceipt : Set where
  field
    provenance : FormalizationProvenance
    kernelReceipt : Set
    statementCorrespondenceReceipt : Set
    dependencyAudit : Set
    mathematicalReview : Set

-- There is deliberately no function FormalizationProvenance -> PromotionReceipt.
-- A provenance record alone does not manufacture kernel, correspondence,
-- dependency, or mathematical-review authority.
