{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisBishopComplexCauchyAlgebraExact where

------------------------------------------------------------------------
-- Source-native algebraic donor for the imaginary exponential
-- Cauchy-product proof on the ACTUAL Bishop complex setoid.
--
-- BishopSetoidComplexExact already owns the carrier, operations and
-- setoid congruence; this module pays the commutative algebra laws
-- needed by a future complex factorial-series/binomial Cauchy proof.
-- No second complex carrier, no assumed field axiom, no postulate.
--
-- NOT YET: analytic complex exponential series convergence, signed
-- factorial Cauchy-product interchange, sine/cosine limit comparison.
------------------------------------------------------------------------

import Real as Bishop
import RealProperties as BishopP
import DASHI.Analysis.BishopSetoidComplexExact as Complex

complexAddCommutative :
  ∀ z w →
  Complex._≈C_
    (Complex._+C_ z w)
    (Complex._+C_ w z)
complexAddCommutative (Complex.complex a b) (Complex.complex c d) =
  Complex.complex-equivalent
    (BishopP.+-comm a c)
    (BishopP.+-comm b d)

complexAddAssociative :
  ∀ z w v →
  Complex._≈C_
    (Complex._+C_ (Complex._+C_ z w) v)
    (Complex._+C_ z (Complex._+C_ w v))
complexAddAssociative
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  Complex.complex-equivalent
    (BishopP.+-assoc a c e)
    (BishopP.+-assoc b d f)

complexMulCommutative :
  ∀ z w →
  Complex._≈C_
    (Complex._*C_ z w)
    (Complex._*C_ w z)
complexMulCommutative
  (Complex.complex a b)
  (Complex.complex c d) =
  Complex.complex-equivalent
    (let open BishopP.ℝ-Solver in
      solve 4
        (λ a b c d →
          (((a ⊗ c) ⊖ (b ⊗ d))
           ⊜ ((c ⊗ a) ⊖ (d ⊗ b))))
        BishopP.≃-refl a b c d)
    (let open BishopP.ℝ-Solver in
      solve 4
        (λ a b c d →
          (((a ⊗ d) ⊕ (b ⊗ c))
           ⊜ ((c ⊗ b) ⊕ (d ⊗ a))))
        BishopP.≃-refl a b c d)

complexMulAssociative :
  ∀ z w v →
  Complex._≈C_
    (Complex._*C_ (Complex._*C_ z w) v)
    (Complex._*C_ z (Complex._*C_ w v))
complexMulAssociative
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  Complex.complex-equivalent
    (let open BishopP.ℝ-Solver in
      solve 6
        (λ a b c d e f →
          ((((a ⊗ c) ⊖ (b ⊗ d)) ⊗ e)
           ⊖ (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ f))
          ⊜
          ((a ⊗ ((c ⊗ e) ⊖ (d ⊗ f)))
           ⊖ (b ⊗ ((c ⊗ f) ⊕ (d ⊗ e)))))
        BishopP.≃-refl a b c d e f)
    (let open BishopP.ℝ-Solver in
      solve 6
        (λ a b c d e f →
          ((((a ⊗ c) ⊖ (b ⊗ d)) ⊗ f)
           ⊕ (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ e))
          ⊜
          ((a ⊗ ((c ⊗ f) ⊕ (d ⊗ e)))
           ⊕ (b ⊗ ((c ⊗ e) ⊖ (d ⊗ f)))))
        BishopP.≃-refl a b c d e f)

complexMulDistributiveLeft :
  ∀ z w v →
  Complex._≈C_
    (Complex._*C_ z (Complex._+C_ w v))
    (Complex._+C_
      (Complex._*C_ z w)
      (Complex._*C_ z v))
complexMulDistributiveLeft
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  Complex.complex-equivalent
    (let open BishopP.ℝ-Solver in
      solve 6
        (λ a b c d e f →
          ((a ⊗ (c ⊕ e)) ⊖ (b ⊗ (d ⊕ f)))
          ⊜
          (((a ⊗ c) ⊖ (b ⊗ d))
           ⊕ ((a ⊗ e) ⊖ (b ⊗ f))))
        BishopP.≃-refl a b c d e f)
    (let open BishopP.ℝ-Solver in
      solve 6
        (λ a b c d e f →
          ((a ⊗ (d ⊕ f)) ⊕ (b ⊗ (c ⊕ e)))
          ⊜
          (((a ⊗ d) ⊕ (b ⊗ c))
           ⊕ ((a ⊗ f) ⊕ (b ⊗ e))))
        BishopP.≃-refl a b c d e f)

complexMulDistributiveRight :
  ∀ z w v →
  Complex._≈C_
    (Complex._*C_ (Complex._+C_ z w) v)
    (Complex._+C_
      (Complex._*C_ z v)
      (Complex._*C_ w v))
complexMulDistributiveRight z w v =
  Complex.≈C-trans
    (complexMulCommutative (Complex._+C_ z w) v)
    (Complex.≈C-trans
      (complexMulDistributiveLeft v z w)
      (Complex.addCongruent
        (complexMulCommutative v z)
        (complexMulCommutative v w)))

-- Original complex algebra's congruence and unit carrier are imported,
-- not redeclared. The above five actual setoid theorems suffice
-- for the purely algebraic rearrangements in a complex finite
-- Cauchy product. The analytic limit step remains separate.
