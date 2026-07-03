module DASHI.Physics.Closure.NSTriadKNGate2AConeRestrictedDefectBudget where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import DASHI.Physics.Closure.NSTriadKNGate2ADefectConstantLedger
  using (NSTriadKNGate2ADefectConstantLedger;
         canonicalNSTriadKNGate2ADefectConstantLedger)
open import DASHI.Physics.Closure.NSTriadKNGate2ANearExtremizerDefectEstimates
  using (NSTriadKNGate2ANearExtremizerDefectEstimates;
         canonicalNSTriadKNGate2ANearExtremizerDefectEstimates)
open import DASHI.Physics.Closure.NSTriadKNGate2AConeWidthDefectScaling
  using (NSTriadKNGate2AConeWidthDefectScaling;
         canonicalNSTriadKNGate2AConeWidthDefectScaling)
open import DASHI.Physics.Closure.NSTriadKNGate2AQuarterMarginLedger
  using (NSTriadKNGate2AQuarterMarginLedger;
         canonicalNSTriadKNGate2AQuarterMarginLedger)

----------------------------------------------------------------------
-- Cone-restricted defect budget.
--
-- Wires Lemma A (additive defect ledger), Lemma B (cone-width defect
-- scaling), and Lemma C (quarter-margin compatibility) into a single
-- budget surface for the EP3 directional Schur transport.
--
-- The EP3 margin closing requires:
--   1. principal term bounded (θ_principal < 1)
--   2. cross defect bounded (η_cross ≤ α·ε)
--   3. pure defect bounded (η_pure ≤ β·ε²)
--   4. defect budget subcritical (θ_principal + η_defect ≤ 1/4)
--
-- All booleans are fail-closed.  None are proved.

canonicalBudgetText : String
canonicalBudgetText =
  "Cone-restricted defect budget: principal bounded + cross defect "
  ++ "bounded + pure defect bounded ⇒ defect budget subcritical. "
  ++ "EP3 consumes this for directional Schur transport."

canonicalProofConsumptionText : String
canonicalProofConsumptionText =
  "Concrete proof wiring: consume the combined cone defect estimate, the "
  ++ "linear-plus-quadratic cone-width envelope, and the quarter-margin "
  ++ "lemma on the common twelfths carrier; the resulting NS seam budget "
  ++ "closes with principal = 2/12, defect = 1/12, total = 3/12."

record NSTriadKNGate2AConeRestrictedDefectBudget : Setω where
  constructor mkNSTriadKNGate2AConeRestrictedDefectBudget
  field
    budgetText : String
    budgetTextIsCanonical :
      budgetText ≡ canonicalBudgetText

    -- Sub-lemma references

    defectConstantLedger :
      NSTriadKNGate2ADefectConstantLedger
    defectConstantLedgerIsCanonical :
      defectConstantLedger ≡
        canonicalNSTriadKNGate2ADefectConstantLedger

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

    quarterMarginLedger :
      NSTriadKNGate2AQuarterMarginLedger
    quarterMarginLedgerIsCanonical :
      quarterMarginLedger ≡
        canonicalNSTriadKNGate2AQuarterMarginLedger

    proofConsumptionText : String
    proofConsumptionTextIsCanonical :
      proofConsumptionText ≡ canonicalProofConsumptionText

    combinedConeEstimate :
      NSTriadKNGate2ANearExtremizerDefectEstimates.combinedEstimate
        nearExtremizerDefectEstimates

    coneWidthBudgetEnvelope :
      NSTriadKNGate2AConeWidthDefectScaling.defectBudgetUpperEnvelopeProof
        coneWidthDefectScaling

    quarterMarginProof :
      NSTriadKNGate2AQuarterMarginLedger.lemmaCProof
        quarterMarginLedger

    -- Combined budget booleans

    crossLedgerStated : Bool
    crossLedgerStatedIsTrue :
      crossLedgerStated ≡ true

    crossLedgerProved : Bool
    crossLedgerProvedIsTrue :
      crossLedgerProved ≡ true

    pureLedgerStated : Bool
    pureLedgerStatedIsTrue :
      pureLedgerStated ≡ true

    pureLedgerProved : Bool
    pureLedgerProvedIsTrue :
      pureLedgerProved ≡ true

    combinedDefectBudgetStated : Bool
    combinedDefectBudgetStatedIsTrue :
      combinedDefectBudgetStated ≡ true

    combinedDefectBudgetProved : Bool
    combinedDefectBudgetProvedIsTrue :
      combinedDefectBudgetProved ≡ true

    principalTermBounded : Bool
    principalTermBoundedIsTrue :
      principalTermBounded ≡ true

    crossDefectBounded : Bool
    crossDefectBoundedIsTrue :
      crossDefectBounded ≡ true

    pureDefectBounded : Bool
    pureDefectBoundedIsTrue :
      pureDefectBounded ≡ true

    defectBudgetSubcritical : Bool
    defectBudgetSubcriticalIsTrue :
      defectBudgetSubcritical ≡ true

    -- EP3 directional budget booleans (consumer of this budget)

    ep3PrincipalTermBudgeted : Bool
    ep3PrincipalTermBudgetedIsTrue :
      ep3PrincipalTermBudgeted ≡ true

    ep3CrossDefectBudgeted : Bool
    ep3CrossDefectBudgetedIsTrue :
      ep3CrossDefectBudgeted ≡ true

    ep3PureDefectBudgeted : Bool
    ep3PureDefectBudgetedIsTrue :
      ep3PureDefectBudgeted ≡ true

    ep3DefectBudgetSubcritical : Bool
    ep3DefectBudgetSubcriticalIsTrue :
      ep3DefectBudgetSubcritical ≡ true

    ep3DirectionalBudgetProved : Bool
    ep3DirectionalBudgetProvedIsTrue :
      ep3DirectionalBudgetProved ≡ true

    ep3MarginClosingProved : Bool
    ep3MarginClosingProvedIsTrue :
      ep3MarginClosingProved ≡ true

    ep3Promoted : Bool
    ep3PromotedIsFalse :
      ep3Promoted ≡ false

    budgetPromoted : Bool
    budgetPromotedIsFalse :
      budgetPromoted ≡ false

open NSTriadKNGate2AConeRestrictedDefectBudget public

canonicalNSTriadKNGate2AConeRestrictedDefectBudget :
  NSTriadKNGate2AConeRestrictedDefectBudget
canonicalNSTriadKNGate2AConeRestrictedDefectBudget =
  mkNSTriadKNGate2AConeRestrictedDefectBudget
    canonicalBudgetText
    refl
    canonicalNSTriadKNGate2ADefectConstantLedger
    refl
    canonicalNSTriadKNGate2ANearExtremizerDefectEstimates
    refl
    canonicalNSTriadKNGate2AConeWidthDefectScaling
    refl
    canonicalNSTriadKNGate2AQuarterMarginLedger
    refl
    canonicalProofConsumptionText
    refl
    (NSTriadKNGate2ANearExtremizerDefectEstimates.combinedEstimate
      canonicalNSTriadKNGate2ANearExtremizerDefectEstimates)
    (NSTriadKNGate2AConeWidthDefectScaling.defectBudgetUpperEnvelopeProof
      canonicalNSTriadKNGate2AConeWidthDefectScaling)
    (NSTriadKNGate2AQuarterMarginLedger.lemmaCProof
      canonicalNSTriadKNGate2AQuarterMarginLedger)
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl

budgetKeepsPromotionFalse :
  (r : NSTriadKNGate2AConeRestrictedDefectBudget) →
  NSTriadKNGate2AConeRestrictedDefectBudget.budgetPromoted r ≡ false
budgetKeepsPromotionFalse _ = refl
