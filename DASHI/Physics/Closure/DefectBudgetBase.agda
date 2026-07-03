module DASHI.Physics.Closure.DefectBudgetBase where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; sym)
open import DASHI.MDL.MDLDescentTradeoff
  using (AddMonoid; OrderedMonoid)

----------------------------------------------------------------------
-- Abstract defect budget.
--
-- DefectBudget packages an ordered commutative monoid (the budget
-- carrier) together with three distinguished constants:
--
--   • η-cross  — cross-defect term   (2⟨ΔJ x, L_neg J_abs x⟩-normalized)
--   • η-pure   — pure-defect term    (⟨ΔJ x, L_neg ΔJ x⟩-normalized)
--   • η-defect — total defect budget (= η-cross + η-pure by definition)
--
-- Lemma A (internal):
--     η-cross + η-pure ≤ η-defect
--
--   Proof: follows directly from the definitional identity
--   η-defect ≡ η-cross + η-pure    and    refl≤ (η-cross + η-pure).
--
-- This record is deliberately abstract — it does not fix N, _+_, or _≤_.
-- The constants and their identity are part of the interface, so that
-- any model of the defect budget automatically inherits Lemma A.

record DefectBudget : Set₁ where
  constructor mkDefectBudget
  field
    orderedMonoid : OrderedMonoid {zero}

  open OrderedMonoid orderedMonoid public
  open AddMonoid M public

  field
    η-cross  : N
    η-pure   : N
    η-defect : N

    η-defect-is-sum : η-defect ≡ η-cross + η-pure

  lemma-a : (η-cross + η-pure) ≤ η-defect
  lemma-a =
    subst (λ z → (η-cross + η-pure) ≤ z) (sym η-defect-is-sum)
      (refl≤ (η-cross + η-pure))

open DefectBudget public
