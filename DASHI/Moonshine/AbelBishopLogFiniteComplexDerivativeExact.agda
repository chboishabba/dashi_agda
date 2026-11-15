module DASHI.Moonshine.AbelBishopLogFiniteComplexDerivativeExact where

------------------------------------------------------------------------
-- FINITE COMPLEX GEOMETRIC CANCELLATION ON THE VENDORED BISHOP REALS.
-- For arbitrary w : BishopComplex and every n : Nat,
--   (1 + w) * sum_{k<n} (-w)^k ~= 1 - (-w)^n.
-- Original source carrier, no analytic authority or postulate.
-- Does NOT identify an infinite derivative or principal logarithm.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra

negativeC : Complex.BishopComplex → Complex.BishopComplex
negativeC w = Algebra._-C_ Algebra.zeroC w

geometricComplexPrefix : Complex.BishopComplex → Nat → Complex.BishopComplex
geometricComplexPrefix w zero = Algebra.zeroC
geometricComplexPrefix w (suc n) =
  Algebra._+C_ (geometricComplexPrefix w n) (Algebra.powC (negativeC w) n)

complexLeftDistributive :
  ∀ a b c →
  Complex._≈C_
    (Algebra._*C_ a (Algebra._+C_ b c))
    (Algebra._+C_ (Algebra._*C_ a b) (Algebra._*C_ a c))
complexLeftDistributive
  (Complex.complex ar ai)
  (Complex.complex br bi)
  (Complex.complex cr ci) =
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a b c d e f →
       ((a ⊗ (c ⊕ e)) ⊖ (b ⊗ (d ⊕ f)))
       ⊜ (((a ⊗ c) ⊖ (b ⊗ d)) ⊕ ((a ⊗ e) ⊖ (b ⊗ f))))
     BishopP.≃-refl ar ai br bi cr ci)
  ,
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a b c d e f →
       ((a ⊗ (d ⊕ f)) ⊕ (b ⊗ (c ⊕ e)))
       ⊜ (((a ⊗ d) ⊕ (b ⊗ c)) ⊕ ((a ⊗ f) ⊕ (b ⊗ e))))
     BishopP.≃-refl ar ai br bi cr ci)

complexFiniteGeometricRemainder :
  ∀ w power →
  Complex._≈C_
    (Algebra._+C_
      (Algebra._-C_ Algebra.oneC power)
      (Algebra._*C_ (Algebra._+C_ Algebra.oneC w) power))
    (Algebra._-C_
      Algebra.oneC
      (Algebra._*C_ (negativeC w) power))
complexFiniteGeometricRemainder
  (Complex.complex wr wi)
  (Complex.complex pr pi) =
  (let open BishopP.ℝ-Solver in
   solve 4
     (λ x y a b →
       ((Κ 1ℚᵘ ⊖ a) ⊕ (((Κ 1ℚᵘ ⊕ x) ⊗ a) ⊖ (y ⊗ b)))
       ⊜ (Κ 1ℚᵘ ⊖ (((Κ 0ℚᵘ ⊖ x) ⊗ a) ⊖ ((Κ 0ℚᵘ ⊖ y) ⊗ b))))
     BishopP.≃-refl wr wi pr pi)
  ,
  (let open BishopP.ℝ-Solver in
   solve 4
     (λ x y a b →
       ((Κ 0ℚᵘ ⊖ b) ⊕ (((Κ 1ℚᵘ ⊕ x) ⊗ b) ⊕ (y ⊗ a)))
       ⊜ (Κ 0ℚᵘ ⊖ (((Κ 0ℚᵘ ⊖ x) ⊗ b) ⊕ ((Κ 0ℚᵘ ⊖ y) ⊗ a))))
     BishopP.≃-refl wr wi pr pi)

originalBishopComplexFiniteLogDerivativeIdentity :
  ∀ w n →
  Complex._≈C_
    (Algebra._*C_
      (Algebra._+C_ Algebra.oneC w)
      (geometricComplexPrefix w n))
    (Algebra._-C_ Algebra.oneC (Algebra.powC (negativeC w) n))
originalBishopComplexFiniteLogDerivativeIdentity
  (Complex.complex wr wi) zero =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ x y →
       (((Κ 1ℚᵘ ⊕ x) ⊗ Κ 0ℚᵘ) ⊖ (y ⊗ Κ 0ℚᵘ))
       ⊜ (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ))
     BishopP.≃-refl wr wi)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ x y →
       (((Κ 1ℚᵘ ⊕ x) ⊗ Κ 0ℚᵘ) ⊕ (y ⊗ Κ 0ℚᵘ))
       ⊜ (Κ 0ℚᵘ ⊖ Κ 0ℚᵘ))
     BishopP.≃-refl wr wi)
originalBishopComplexFiniteLogDerivativeIdentity w (suc n) =
  let
    prefix = geometricComplexPrefix w n
    power = Algebra.powC (negativeC w) n
    step = complexLeftDistributive
      (Algebra._+C_ Algebra.oneC w) prefix power
    induction = originalBishopComplexFiniteLogDerivativeIdentity w n
    combined = Algebra.addCCongruent induction (Complex.≈C-refl _)
    finish = complexFiniteGeometricRemainder w power
  in
  (BishopP.≃-trans (proj₁ step)
    (BishopP.≃-trans (proj₁ combined) (proj₁ finish)))
  ,
  (BishopP.≃-trans (proj₂ step)
    (BishopP.≃-trans (proj₂ combined) (proj₂ finish)))
