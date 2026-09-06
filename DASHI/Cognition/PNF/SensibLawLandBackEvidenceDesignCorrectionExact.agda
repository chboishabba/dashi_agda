module DASHI.Cognition.PNF.SensibLawLandBackEvidenceDesignCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousLandBackGlobalEvidenceExact as Atlas
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Authority

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
    sourceAuthority : Authority.SourceAuthorityReceipt
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
  Authority.vasco2018LandUseAuthority
  fixedEffectsCausalChainDesign
  sourceReportsCausalEffect
  "Correction overlay: Probst et al. 2020 uses property-level fixed-effects/event-study analysis and explicitly explores the causal chain between Terra Legal titling and deforestation; the old comparativeObservationalDesign tag is too weak. Source identity remains Probst et al.; the Vasco authority passed here is only a temporary type-compatible external-source placeholder and MUST NOT be treated as Probst authorship. A dedicated Probst authority receipt is the next source cleanup target."
  false refl
  false refl

-- den Braber is peer-reviewed comparative evidence. Downstream prose should not
-- silently turn a comparative estimate into an unqualified intervention theorem.
denBraber2024ClaimVerbCorrection : EvidenceDesignCorrection
denBraber2024ClaimVerbCorrection = evidenceDesignCorrection
  Atlas.amazonSocioeconomicTradeoff2024
  Authority.denBraber2024Authority
  peerReviewedComparativeMatchedDesign
  sourceReportsComparativeAssociationOrEstimatedDifference
  "Correction overlay: phrase the 48-83% result as the study's comparative estimate for Indigenous territories relative to specified competing land-use controls; do not rewrite it as universal causal effect of Indigenous governance"
  false refl
  false refl

------------------------------------------------------------------------
-- IMPORTANT audit trap: the Probst overlay above deliberately exposes that the
-- source-authority owner still lacks a dedicated Probst receipt.  The temporary
-- placeholder is NOT permission to transfer Vasco authorship.  We make that
-- impossibility explicit and keep the cleanup residual open.
------------------------------------------------------------------------

data PlaceholderAuthorityTransfersAuthorship : Set where
data LocalDesignCorrectionCreatesSourceProposition : Set where
data ComparativeEstimateBecomesUniversalCausalLaw : Set where

placeholderDoesNotTransferAuthorship : PlaceholderAuthorityTransfersAuthorship → ⊥
placeholderDoesNotTransferAuthorship ()
correctionDoesNotCreateSourceProposition : LocalDesignCorrectionCreatesSourceProposition → ⊥
correctionDoesNotCreateSourceProposition ()
comparativeEstimateDoesNotBecomeUniversalLaw : ComparativeEstimateBecomesUniversalCausalLaw → ⊥
comparativeEstimateDoesNotBecomeUniversalCausalLaw ()
