module DASHI.Foundations.BishopFiniteRatioBudgetExact where

------------------------------------------------------------------------
-- UNIFORM FINITE COEFFICIENT MASS BY A SINGLE RATIO BUDGET.
--
-- If c_(n+1) <= q*c_n, c_n >=0, B>=0 and 1+B*q = B,
-- then ALL true Bishop `Sequence.SeriesOf c n` are bounded by
-- B*c_0.  No infinite sum, reciprocals or unproved geometric
-- series constructor. The induction uses the future-tail BANK
-- S_n + B*c_n <= B*c_0, not only a pointwise geometric guess.
--
-- For original CMP102 use qA=1/12, B_A=12/11, cA0=1/2;
-- qB=1/20, B_B=20/19, cB0=1/6. Thus explicit ceilings
-- are 6/11 and 10/57. The ORIGINAL factorial step ratios,
-- embedding/order checks and rational fixed points remain
-- source-specific donors, not assumed for unrelated coefficients.
--
-- Source-written pending pinned Bishop Agda compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq

finiteRatioBudgetInvariant :
  (coefficient : Nat → R.ℝ) (ratio budget : R.ℝ) →
  R.NonNegative budget →
  (∀ n → R.NonNegative (coefficient n)) →
  (∀ n → R._≤_ (coefficient (suc n))
    (R._*_ ratio (coefficient n))) →
  R._≃_ (R._+_ R.1ℝ (R._*_ budget ratio)) budget →
  ∀ count →
  R._≤_
    (R._+_ (Seq.SeriesOf coefficient count)
      (R._*_ budget (coefficient count)))
    (R._*_ budget (coefficient zero))
finiteRatioBudgetInvariant coeff ratio budget hB hpos hstep hfixed zero =
  P.≤-reflexive
    (P.+-identityˡ (R._*_ budget (coeff zero)))
finiteRatioBudgetInvariant coeff ratio budget hB hpos hstep hfixed (suc n) =
  let
    S = Seq.SeriesOf coeff n
    c = coeff n
    cnext = coeff (suc n)
    futureBound =
      P.*-monoˡ-≤-nonNeg (hstep n) hB
    reassociate =
      let open P.ℝ-Solver
      in solve 4
        (λ s c b q →
          (s ⊕ c) ⊕ (b ⊗ (q ⊗ c))
          ⊜ s ⊕ ((Κ 1ℚᵘ ⊕ (b ⊗ q)) ⊗ c))
        P.≃-refl S c budget ratio
  in
  P.≤-trans
    (P.+-mono-≤ P.≤-refl futureBound)
    (P.≤-respˡ-≃
      (P.≃-trans reassociate
        (P.+-congˡ S (P.*-congʳ hfixed)))
      (finiteRatioBudgetInvariant coeff ratio budget
        hB hpos hstep hfixed n))

finiteRatioAllPrefixesBounded :
  (coefficient : Nat → R.ℝ) (ratio budget : R.ℝ) →
  R.NonNegative budget →
  (∀ n → R.NonNegative (coefficient n)) →
  (∀ n → R._≤_ (coefficient (suc n))
    (R._*_ ratio (coefficient n))) →
  R._≃_ (R._+_ R.1ℝ (R._*_ budget ratio)) budget →
  ∀ count →
  R._≤_ (Seq.SeriesOf coefficient count)
    (R._*_ budget (coefficient zero))
finiteRatioAllPrefixesBounded coeff ratio budget hB hpos hstep hfixed n =
  let
    partial = Seq.SeriesOf coeff n
    outstanding = R._*_ budget (coeff n)
    hnonneg = P.nonNegx,y⇒nonNegx*y hB (hpos n)
    hlo = P.≤-respˡ-≃
      (P.≃-symm (P.+-identityʳ partial))
      (P.+-monoʳ-≤ partial
        (P.nonNegx⇒0≤x hnonneg))
  in
  P.≤-trans hlo
    (finiteRatioBudgetInvariant
      coeff ratio budget hB hpos hstep hfixed n)
