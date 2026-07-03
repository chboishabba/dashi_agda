module DASHI.Physics.Closure.NSTriadKNGate2ADefectConstantLedger where

open import Agda.Primitive using (Setω; Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import DASHI.Physics.Closure.DefectBudgetBase
  using (DefectBudget; lemma-a)
open import DASHI.Physics.Closure.NSTriadKNGate2ASeamBudgetArithmetic
  using (canonicalGate2ADefectBudget)

----------------------------------------------------------------------
-- Lemma A: additive defect ledger.
--
-- Claim:
--   η_cross + η_pure ≤ η_defect.
--
-- This is the bookkeeping inequality that aggregates the cross-defect
-- and pure-defect contributions into a single defect budget.
--
--   η_cross  = sup_{x∈𝒮_N(ε)} 2⟨ΔJ x, L_neg J_abs x⟩ / ⟨J_abs x, L_neg J_abs x⟩
--   η_pure   = sup_{x∈𝒮_N(ε)} ⟨ΔJ x, L_neg ΔJ x⟩ / ⟨J_abs x, L_neg J_abs x⟩
--   η_defect = η_cross + η_pure   (definition)
--
-- Lemma A follows directly from the definitional identity:
--   η-defect-is-sum : η-defect ≡ η-cross + η-pure
--   lemma-a : (η-cross + η-pure) ≤ η-defect    (by refl≤ + substitution)
--
-- Status: Lemma A is structurally proved (inhabitanted via the abstract
-- DefectBudget interface).  The ledger as a whole is not promoted.

-- The canonical budget is abstract — the constants η-cross, η-pure,
-- η-defect and their identity are postulated from the Gate 2-A
-- definition.  Lemma A follows structurally from that identity.

open DefectBudget canonicalGate2ADefectBudget

canonicalLedgerText : String
canonicalLedgerText =
  "Additive defect ledger: η_cross + η_pure ≤ η_defect."

canonicalLedgerTargetText : String
canonicalLedgerTargetText =
  "η_cross + η_pure ≤ η_defect, where η_cross bounds the cross term "
  ++ "2⟨ΔJ x, L_neg J_abs x⟩ and η_pure bounds ⟨ΔJ x, L_neg ΔJ x⟩, "
  ++ "both normalized by ⟨J_abs x, L_neg J_abs x⟩."

canonicalScopeText : String
canonicalScopeText =
  "Inequality holds pointwise for x ∈ 𝒮_N(ε).  The sup over the cone "
  ++ "preserves the additive bound."

record NSTriadKNGate2ADefectConstantLedger : Setω where
  constructor mkNSTriadKNGate2ADefectConstantLedger
  field
    defectBudget : DefectBudget
    defectBudgetIsCanonical :
      defectBudget ≡ canonicalGate2ADefectBudget

    lemmaAProof : lemma-a defectBudget

    ledgerText : String
    ledgerTextIsCanonical :
      ledgerText ≡ canonicalLedgerText

    targetText : String
    targetTextIsCanonical :
      targetText ≡ canonicalLedgerTargetText

    scopeText : String
    scopeTextIsCanonical :
      scopeText ≡ canonicalScopeText

    etaCrossPureAdditiveLedgerStated : Bool
    etaCrossPureAdditiveLedgerStatedIsTrue :
      etaCrossPureAdditiveLedgerStated ≡ true

    etaCrossPureAdditiveLedgerProved : Bool
    etaCrossPureAdditiveLedgerProvedIsTrue :
      etaCrossPureAdditiveLedgerProved ≡ true

    ledgerPromoted : Bool
    ledgerPromotedIsFalse :
      ledgerPromoted ≡ false

open NSTriadKNGate2ADefectConstantLedger public

----------------------------------------------------------------------
-- Lemma A is now structurally proved.
--
--   defectBudget = canonicalGate2ADefectBudget  (postulated Gate 2-A)
--   lemmaAProof  = lemma-a canonicalGate2ADefectBudget
--                : (η-cross + η-pure) ≤ η-defect
--
-- etaCrossPureAdditiveLedgerProved = true  (the proof term exists).
-- ledgerPromoted                  = false (whole ledger not promoted).

canonicalNSTriadKNGate2ADefectConstantLedger :
  NSTriadKNGate2ADefectConstantLedger
canonicalNSTriadKNGate2ADefectConstantLedger =
  mkNSTriadKNGate2ADefectConstantLedger
    canonicalGate2ADefectBudget
    refl
    (lemma-a canonicalGate2ADefectBudget)
    canonicalLedgerText
    refl
    canonicalLedgerTargetText
    refl
    canonicalScopeText
    refl
    true
    refl
    true
    refl
    false
    refl

ledgerKeepsPromotionFalse :
  (r : NSTriadKNGate2ADefectConstantLedger) →
  NSTriadKNGate2ADefectConstantLedger.ledgerPromoted r ≡ false
ledgerKeepsPromotionFalse _ = refl
