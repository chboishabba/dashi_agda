module DASHI.Physics.YangMills.BalabanP0TransverseTensorNotAutomaticallyScalarProjectorExact where

-- Mathematical negative control for an unjustified P0.5 promotion:
--   "Ward transversality + parity => every finite-momentum tensor is
--    exactly one scalar times the isotropic transverse projector".
--
-- At lattice momentum k=(1,2,0,0), set s=Σ k_i²,
--   P_ij = s δ_ij - k_i k_j,
--   T_ij = Σ_a k_a² P_ia P_aj.
-- The resulting T is symmetric, transverse and even in k.
-- Yet T_00=32 and T_22=0 whereas P_00=4 and P_22=5.
-- Therefore T cannot be a scalar multiple of P at this momentum.
--
-- The polynomial construction is also covariant under signed axis
-- permutations if k and both Lorentz indices transform together:
-- this formal file proves the concrete rational transversality and
-- failure of scalar factorization. Global B4 covariance follows from
-- the formula but is NOT promoted as a kernel-checked Agda theorem.
--
-- CMP109 needs only the QUADRATIC external-momentum two-jet projector
-- with an O(derivative^3) remainder, not an exact all-k scalar factor.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval

k : Eval.AxisIndex → ℚ
k Eval.axis0 = + 1 / 1
k Eval.axis1 = + 2 / 1
k Eval.axis2 = 0ℚ
k Eval.axis3 = 0ℚ

delta : Eval.AxisIndex → Eval.AxisIndex → ℚ
delta Eval.axis0 Eval.axis0 = 1ℚ
delta Eval.axis0 Eval.axis1 = 0ℚ
delta Eval.axis0 Eval.axis2 = 0ℚ
delta Eval.axis0 Eval.axis3 = 0ℚ
delta Eval.axis1 Eval.axis0 = 0ℚ
delta Eval.axis1 Eval.axis1 = 1ℚ
delta Eval.axis1 Eval.axis2 = 0ℚ
delta Eval.axis1 Eval.axis3 = 0ℚ
delta Eval.axis2 Eval.axis0 = 0ℚ
delta Eval.axis2 Eval.axis1 = 0ℚ
delta Eval.axis2 Eval.axis2 = 1ℚ
delta Eval.axis2 Eval.axis3 = 0ℚ
delta Eval.axis3 Eval.axis0 = 0ℚ
delta Eval.axis3 Eval.axis1 = 0ℚ
delta Eval.axis3 Eval.axis2 = 0ℚ
delta Eval.axis3 Eval.axis3 = 1ℚ

squaredNorm : ℚ
squaredNorm = k Eval.axis0 * k Eval.axis0
  + k Eval.axis1 * k Eval.axis1
  + k Eval.axis2 * k Eval.axis2
  + k Eval.axis3 * k Eval.axis3

P : Eval.AxisIndex → Eval.AxisIndex → ℚ
P i j = squaredNorm * delta i j - k i * k j

T : Eval.AxisIndex → Eval.AxisIndex → ℚ
T i j =
  ((k Eval.axis0 * k Eval.axis0) * P i Eval.axis0) * P Eval.axis0 j
  + ((k Eval.axis1 * k Eval.axis1) * P i Eval.axis1) * P Eval.axis1 j
  + ((k Eval.axis2 * k Eval.axis2) * P i Eval.axis2) * P Eval.axis2 j
  + ((k Eval.axis3 * k Eval.axis3) * P i Eval.axis3) * P Eval.axis3 j

contractT : Eval.AxisIndex → ℚ
contractT j =
  k Eval.axis0 * T Eval.axis0 j
  + k Eval.axis1 * T Eval.axis1 j
  + k Eval.axis2 * T Eval.axis2 j
  + k Eval.axis3 * T Eval.axis3 j

-- Actual rational Ward contraction on ALL four tensor columns.
contractTIsZero : ∀ j → contractT j ≡ 0ℚ
contractTIsZero Eval.axis0 = refl
contractTIsZero Eval.axis1 = refl
contractTIsZero Eval.axis2 = refl
contractTIsZero Eval.axis3 = refl

P00Is4 : P Eval.axis0 Eval.axis0 ≡ (+ 4 / 1)
P00Is4 = refl

P22Is5 : P Eval.axis2 Eval.axis2 ≡ (+ 5 / 1)
P22Is5 = refl

T00Is32 : T Eval.axis0 Eval.axis0 ≡ (+ 32 / 1)
T00Is32 = refl

T22Is0 : T Eval.axis2 Eval.axis2 ≡ 0ℚ
T22Is0 = refl

-- If T=c*P for any rational c, these cross-products must agree.
-- In the concrete, physically permitted transverse example 160 != 0.
crossProductsAreDifferent :
  (T Eval.axis0 Eval.axis0 * P Eval.axis2 Eval.axis2)
  ≢
  (T Eval.axis2 Eval.axis2 * P Eval.axis0 Eval.axis0)
crossProductsAreDifferent ()

noUniversalScalarProjectorAtThisMomentum :
  (c : ℚ) →
  T Eval.axis0 Eval.axis0 ≡ c * P Eval.axis0 Eval.axis0 →
  T Eval.axis2 Eval.axis2 ≡ c * P Eval.axis2 Eval.axis2 →
  ⊥
noUniversalScalarProjectorAtThisMomentum c h00 h22 =
  crossProductsAreDifferent
    (trans
      (cong (λ v → v * P Eval.axis2 Eval.axis2) h00)
      (trans
        (Ring.solve-∀ c)
        (sym (cong (λ v → v * P Eval.axis0 Eval.axis0) h22))))

-- This is a correctness gate, not a counterexample to CMP109:
-- its source only requires the right off-diagonal quadratic two-jet.
