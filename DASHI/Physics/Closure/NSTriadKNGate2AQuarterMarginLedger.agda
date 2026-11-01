module DASHI.Physics.Closure.NSTriadKNGate2AQuarterMarginLedger where

open import Agda.Primitive using (Set; lzero; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import DASHI.Physics.Closure.NSTriadKNGate2AConeWidthDefectScaling
  using ( NSTriadKNGate2AConeWidthDefectScaling
        ; canonicalNSTriadKNGate2AConeWidthDefectScaling
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ANearExtremizerDefectEstimates
  using ( NSTriadKNGate2ANearExtremizerDefectEstimates
        ; canonicalNSTriadKNGate2ANearExtremizerDefectEstimates
        )
open import DASHI.Physics.Closure.QuarterMarginBase
  using (QuarterMarginModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ASeamBudgetArithmetic
  using (canonicalQuarterMarginModel)

----------------------------------------------------------------------
-- Lemma C: quarter-margin compatibility ledger.
--
-- Claim:
--   θ_principal + η_defect(ε) ≤ 1/4.
--
-- Here:
--   θ_principal = sup_{x∈𝒮_N(ε)} ⟨J_abs x, L_neg J_abs x⟩ / ⟨J_abs x, L_abs J_abs x⟩
--   η_defect = η_cross + η_pure (from Lemma A)
--
-- Slack budget (observed):
--   θ_N ≈ 1/6   ⇒   slack = 1/4 − 1/6 = 1/12 ≈ 0.0833.
--
-- Abstract ledger target:
--   θ_principal ≤ 1/6
--   η_defect    ≤ 1/12
--   θ_principal + η_defect ≤ 1/4.
--
-- Status:
--   Abstract model: proved (the inequalities hold as model fields).
--   Seam-local carrier instantiation: proved by consuming Lemma A and
--   Lemma B on the shared twelfths carrier.
--   Exact operator-level NS closure: still open elsewhere.

open QuarterMarginModel canonicalQuarterMarginModel

canonicalLedgerText : String
canonicalLedgerText =
  "Quarter-margin compatibility: θ_principal + η_defect ≤ 1/4."

canonicalObservedSlackText : String
canonicalObservedSlackText =
  "Observed θ_N ≈ 1/6.  Slack to 1/4 is 1/12 ≈ 0.0833."

canonicalTargetText : String
canonicalTargetText =
  "Abstract target: θ_principal ≤ 1/6 and η_defect ≤ 1/12, so the sum "
  ++ "fits under the quarter-margin threshold."

canonicalBudgetText : String
canonicalBudgetText =
  "Seam-local quarter-margin closure in twelfths: θ_principal = 2/12, "
  ++ "η_defect = 1/12, and one-quarter = 3/12, so the budget closes by "
  ++ "the exact identity 2 + 1 = 3 on the common carrier."

record NSTriadKNGate2AQuarterMarginLedger : Set (lsuc lzero) where
  constructor mkNSTriadKNGate2AQuarterMarginLedger
  field
    nearExtremizerDefectEstimates :
      NSTriadKNGate2ANearExtremizerDefectEstimates
    nearExtremizerDefectEstimatesIsCanonical :
      nearExtremizerDefectEstimates ≡
        canonicalNSTriadKNGate2ANearExtremizerDefectEstimates

    coneWidthDefectScaling :
      NSTriadKNGate2AConeWidthDefectScaling
    coneWidthDefectScalingIsCanonical :
      coneWidthDefectScaling ≡
        canonicalNSTriadKNGate2AConeWidthDefectScaling

    quarterMarginModel : QuarterMarginModel
    quarterMarginModelIsCanonical :
      quarterMarginModel ≡ canonicalQuarterMarginModel

    lemmaCProof :
      QuarterMarginModel._≤_ quarterMarginModel
        (QuarterMarginModel._+_ quarterMarginModel
          (QuarterMarginModel.θ-principal quarterMarginModel)
          (QuarterMarginModel.η-defect quarterMarginModel))
        (QuarterMarginModel.one-quarter quarterMarginModel)

    ledgerText : String
    ledgerTextIsCanonical :
      ledgerText ≡ canonicalLedgerText

    observedSlackText : String
    observedSlackTextIsCanonical :
      observedSlackText ≡ canonicalObservedSlackText

    targetText : String
    targetTextIsCanonical :
      targetText ≡ canonicalTargetText

    budgetText : String
    budgetTextIsCanonical :
      budgetText ≡ canonicalBudgetText

    quarterMarginAbstractModelProved : Bool
    quarterMarginAbstractModelProvedIsTrue :
      quarterMarginAbstractModelProved ≡ true

    quarterMarginCompatibilityStated : Bool
    quarterMarginCompatibilityStatedIsTrue :
      quarterMarginCompatibilityStated ≡ true

    quarterMarginCompatibilityProved : Bool
    quarterMarginCompatibilityProvedIsTrue :
      quarterMarginCompatibilityProved ≡ true

    marginLedgerPromoted : Bool
    marginLedgerPromotedIsFalse :
      marginLedgerPromoted ≡ false

open NSTriadKNGate2AQuarterMarginLedger public

canonicalNSTriadKNGate2AQuarterMarginLedger :
  NSTriadKNGate2AQuarterMarginLedger
canonicalNSTriadKNGate2AQuarterMarginLedger =
  mkNSTriadKNGate2AQuarterMarginLedger
    canonicalNSTriadKNGate2ANearExtremizerDefectEstimates
    refl
    canonicalNSTriadKNGate2AConeWidthDefectScaling
    refl
    canonicalQuarterMarginModel
    refl
    (QuarterMarginModel.lemma-c canonicalQuarterMarginModel)
    canonicalLedgerText
    refl
    canonicalObservedSlackText
    refl
    canonicalTargetText
    refl
    canonicalBudgetText
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl

marginLedgerKeepsPromotionFalse :
  (r : NSTriadKNGate2AQuarterMarginLedger) →
  NSTriadKNGate2AQuarterMarginLedger.marginLedgerPromoted r ≡ false
marginLedgerKeepsPromotionFalse r =
  NSTriadKNGate2AQuarterMarginLedger.marginLedgerPromotedIsFalse r
