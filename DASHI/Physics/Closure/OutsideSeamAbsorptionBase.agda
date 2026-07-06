module DASHI.Physics.Closure.OutsideSeamAbsorptionBase where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; sym; trans)
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)

----------------------------------------------------------------------
-- Exact outside-seam absorption kernel.
--
-- This records the analytic shape needed after the exact K_N(A) transfer:
--
--   total-leakage = exact-kna-ratio + outside-seam-pollution
--
-- together with a uniform domination of the outside-seam contribution by
-- an absorbable budget.  If the absorbed budget still fits under the same
-- quarter threshold, then the total leakage closes on the true carrier.
--
-- The sharp special case is the no-pollution theorem:
--
--   outside-seam-pollution = 0#
--
-- in which case total leakage collapses exactly to the transported K_N(A)
-- leakage lane.

record OutsideSeamAbsorptionModel : Set₁ where
  constructor mkOutsideSeamAbsorptionModel
  field
    exactTransferModel : ExactKNAOperatorTransferModel

  open ExactKNAOperatorTransferModel exactTransferModel public

  field
    outside-seam-pollution : N
    absorbable-outside-budget : N
    total-leakage : N

    totalDecomposition :
      total-leakage ≡
      (exact-kna-ratio + outside-seam-pollution)

    outside≤absorbed :
      outside-seam-pollution ≤ absorbable-outside-budget

    exactPlusAbsorbed≤quarter :
      (exact-kna-ratio + absorbable-outside-budget) ≤ one-quarter

    absorbedOutsideVanishes :
      absorbable-outside-budget ≡ 0#

  total≤quarter : total-leakage ≤ one-quarter
  total≤quarter =
    subst
      (λ t → t ≤ one-quarter)
      (sym totalDecomposition)
      (trans≤
        (exact-kna-ratio + outside-seam-pollution)
        (exact-kna-ratio + absorbable-outside-budget)
        one-quarter
        (mono+
          exact-kna-ratio
          exact-kna-ratio
          outside-seam-pollution
          absorbable-outside-budget
          (refl≤ exact-kna-ratio)
          outside≤absorbed)
        exactPlusAbsorbed≤quarter)

  total≤quarter-viaExactDirectional :
    total-leakage ≤ one-quarter
  total≤quarter-viaExactDirectional =
    total≤quarter

  exactPlusZero≤quarter :
    (exact-kna-ratio + 0#) ≤ one-quarter
  exactPlusZero≤quarter =
    subst
      (λ t → (exact-kna-ratio + t) ≤ one-quarter)
      absorbedOutsideVanishes
      exactPlusAbsorbed≤quarter

  outside≤zero :
    outside-seam-pollution ≤ 0#
  outside≤zero =
    subst
      (λ t → outside-seam-pollution ≤ t)
      absorbedOutsideVanishes
      outside≤absorbed

  totalDecompositionWithZeroBudget :
    total-leakage ≡
    (exact-kna-ratio + outside-seam-pollution)
  totalDecompositionWithZeroBudget =
    totalDecomposition

  totalEqualsExactWhenOutsideZero :
    outside-seam-pollution ≡ 0# →
    total-leakage ≡ (exact-kna-ratio + 0#)
  totalEqualsExactWhenOutsideZero outsideZero =
    subst
      (λ t → total-leakage ≡ (exact-kna-ratio + t))
      outsideZero
      totalDecomposition

open OutsideSeamAbsorptionModel public
