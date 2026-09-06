module DASHI.Cognition.PNF.SensibLawLandBackEvidenceDesignCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousLandBackGlobalEvidenceExact as Atlas

------------------------------------------------------------------------
-- Additive corrections to local design/claim labels in the first global atlas.
-- The original receipts remain historical branch objects; new consumers should
-- use these corrected overlays where the earlier local label was too coarse.
------------------------------------------------------------------------

data PreferredDesignKind : Set where
  fixedEffectsCausalChainDesign
  peerReviewedComparativeMatchedDesign
  : PreferredDesignKind

data ClaimVerbBoundary : Set where
  sourceReportsCausalEffect
  sourceReportsComparativeAssociationOrEstimatedDifference
  : ClaimVerbBoundary

record EvidenceDesignCorrection : Set where
  constructor evidenceDesignCorrection
  field
    historicalStudy : Atlas.LandBackStudyReceipt
    correctedSourceCitation : String
    preferredDesign : PreferredDesignKind
    preferredClaimVerb : ClaimVerbBoundary
    correctionReference : String
    historicalReceiptDeleted : Bool
    historicalReceiptDeletedIsFalse : historicalReceiptDeleted ≡ false
    universalCausalPromotion : Bool
    universalCausalPromotionIsFalse : universalCausalPromotion ≡ false
open EvidenceDesignCorrection public

probst2020DesignCorrection : EvidenceDesignCorrection
probst2020DesignCorrection = evidenceDesignCorrection
  Atlas.probst2020PrivateTitlingCounterexample
  "Probst et al., Impacts of a large-scale titling initiative on deforestation in the Brazilian Amazon, Nature Sustainability 3 (2020) 1019-1026, doi:10.1038/s41893-020-0537-2"
  fixedEffectsCausalChainDesign
  sourceReportsCausalEffect
  "Correction overlay: Probst et al. use property-level fixed-effects/event-study analysis and explicitly explore the causal chain between Terra Legal titling and deforestation; the old comparativeObservationalDesign local tag is too weak. This overlay uses Probst's own source identity only."
  false refl
  false refl

-- den Braber is peer-reviewed comparative evidence. Downstream prose should not
-- silently turn a comparative estimate into an unqualified intervention theorem.
denBraber2024ClaimVerbCorrection : EvidenceDesignCorrection
denBraber2024ClaimVerbCorrection = evidenceDesignCorrection
  Atlas.amazonSocioeconomicTradeoff2024
  "den Braber et al., Nature Ecology & Evolution 8 (2024) 1482-1492, doi:10.1038/s41559-024-02458-w"
  peerReviewedComparativeMatchedDesign
  sourceReportsComparativeAssociationOrEstimatedDifference
  "Correction overlay: phrase the 48-83% result as the study's comparative estimate for Indigenous territories relative to specified competing land-use controls; do not rewrite it as a universal causal effect of Indigenous governance"
  false refl
  false refl

------------------------------------------------------------------------
-- No source-identity substitution is permitted by a correction overlay.
------------------------------------------------------------------------

data LocalDesignCorrectionCreatesSourceProposition : Set where
data ComparativeEstimateBecomesUniversalCausalLaw : Set where
data CorrectionOverlayTransfersForeignAuthorship : Set where

correctionDoesNotCreateSourceProposition : LocalDesignCorrectionCreatesSourceProposition → ⊥
correctionDoesNotCreateSourceProposition ()
comparativeEstimateDoesNotBecomeUniversalLaw : ComparativeEstimateBecomesUniversalCausalLaw → ⊥
comparativeEstimateDoesNotBecomeUniversalCausalLaw ()
correctionDoesNotTransferForeignAuthorship : CorrectionOverlayTransfersForeignAuthorship → ⊥
correctionDoesNotTransferForeignAuthorship ()
