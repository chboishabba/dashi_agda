module DASHI.Mathematics.Automorphic.EllipticCMNormalizedOneDimensionalQSeriesExact where

------------------------------------------------------------------------
-- K4: AVOID ALL-PRIME RECONSTRUCTION WHEN dim S₂(Γ₀(32)) = 1.
--
-- For any TWO actual rational Fourier coefficient families f_n,g_n,
-- if the genuine one-dimensional modular-form theorem provides
-- the SAME scalar c with f_n = c*g_n for EVERY n, and both are
-- normalized by f_1=g_1=1, then c=1 and EVERY coefficient matches.
--
-- This is a real all-n algebraic proof, not a copied finite set
-- of equality receipts. It leaves proportionality as the EXACT
-- geometric/analytic dimension-one theorem premise; it does not
-- claim to construct the level-32 modular-form space in Agda.
--
-- Intended original specialization:
--   f_n := coefficient of the actual E:y²=x³-x modular newform,
--   g_n := [q^n] eta(4τ)² eta(8τ)².
-- The selected E modularity and analytic eta cusp-space equality
-- are still source obligations, not inhabited by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record NormalizedOneDimensionalQSeries
    (f g : Nat → ℚ) : Set where
  field
    proportionalityScalar : ℚ
    genuineDimensionOneProportionality :
      (n : Nat) →
      f n ≡ proportionalityScalar * g n
    originalNormalizedFirstCoefficient : f 1 ≡ 1ℚ
    etaNormalizedFirstCoefficient : g 1 ≡ 1ℚ

open NormalizedOneDimensionalQSeries public

normalizedScalarIsOne :
  ∀ {f g} →
  (data : NormalizedOneDimensionalQSeries f g) →
  proportionalityScalar data ≡ 1ℚ
normalizedScalarIsOne data =
  trans (sym (solve (proportionalityScalar data ∷ [])))
    (sym firstIsScalar)
  where
    firstIsScalar :
      1ℚ ≡ proportionalityScalar data * 1ℚ
    firstIsScalar =
      trans
        (sym (originalNormalizedFirstCoefficient data))
        (trans
          (genuineDimensionOneProportionality data 1)
          (cong (λ x → proportionalityScalar data * x)
            (etaNormalizedFirstCoefficient data)))

normalizedOneDimensionalAllNCoefficientsAgree :
  ∀ {f g} →
  (data : NormalizedOneDimensionalQSeries f g) →
  (n : Nat) → f n ≡ g n
normalizedOneDimensionalAllNCoefficientsAgree {f} {g} data n =
  trans
    (genuineDimensionOneProportionality data n)
    (trans
      (cong (λ scalar → scalar * g n)
        (normalizedScalarIsOne data))
      (solve (g n ∷ [])))
