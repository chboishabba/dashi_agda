module DASHI.Reasoning.H06BishopAffineFrameExact where

-- H06 actual Bishop reals, not rational substitutes or propositional
-- equality of Cauchy representatives. No kernel acceptance claimed.
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as RatP
import Real as B
import RealProperties as BP
import Inverse as Inv
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Rec

-- The actual original two-pivot normalization, with apartness instead of
-- merely negated equality. A signed pivot can be either positive or negative.
det2 : B.ℝ → B.ℝ → B.ℝ → B.ℝ → B.ℝ
det2 a b c d = B._-_ (B._*_ a d) (B._*_ b c)

record Pivot2 : Set where
  constructor pivot2
  field
    a b c d : B.ℝ
    admissible : B._≄0 (det2 a b c d)
open Pivot2 public

firstCoordinate secondCoordinate : Pivot2 → B.ℝ → B.ℝ → B.ℝ
firstCoordinate (pivot2 a b c d nz) u v =
  B._*_ (Inv._⁻¹ (det2 a b c d) nz)
    (B._-_ (B._*_ d u) (B._*_ b v))
secondCoordinate (pivot2 a b c d nz) u v =
  B._*_ (Inv._⁻¹ (det2 a b c d) nz)
    (B._-_ (B._*_ a v) (B._*_ c u))

firstNumeratorReconstruct : (a b c d u v i : B.ℝ) → B._≃_ (B._+_ (B._*_ a (B._*_ i (B._-_ (B._*_ d u) (B._*_ b v)))) (B._*_ b (B._*_ i (B._-_ (B._*_ a v) (B._*_ c u))))) (B._*_ (B._*_ (B._-_ (B._*_ a d) (B._*_ b c)) i) u)
firstNumeratorReconstruct a b c d u v i =
  let open BP.ℝ-Solver in
  solve 7 (λ a b c d u v i → ((a ⊗ (i ⊗ ((d ⊗ u) ⊖ (b ⊗ v)))) ⊕ (b ⊗ (i ⊗ ((a ⊗ v) ⊖ (c ⊗ u))))) ⊜ ((((a ⊗ d) ⊖ (b ⊗ c)) ⊗ i) ⊗ u))
    BP.≃-refl a b c d u v i

secondNumeratorReconstruct : (a b c d u v i : B.ℝ) → B._≃_ (B._+_ (B._*_ c (B._*_ i (B._-_ (B._*_ d u) (B._*_ b v)))) (B._*_ d (B._*_ i (B._-_ (B._*_ a v) (B._*_ c u))))) (B._*_ (B._*_ (B._-_ (B._*_ a d) (B._*_ b c)) i) v)
secondNumeratorReconstruct a b c d u v i =
  let open BP.ℝ-Solver in
  solve 7 (λ a b c d u v i → ((c ⊗ (i ⊗ ((d ⊗ u) ⊖ (b ⊗ v)))) ⊕ (d ⊗ (i ⊗ ((a ⊗ v) ⊖ (c ⊗ u))))) ⊜ ((((a ⊗ d) ⊖ (b ⊗ c)) ⊗ i) ⊗ v))
    BP.≃-refl a b c d u v i

firstReconstruct : (p : Pivot2) (u v : B.ℝ) →
  B._≃_ (B._+_ (B._*_ (a p) (firstCoordinate p u v))
                   (B._*_ (b p) (secondCoordinate p u v))) u
firstReconstruct (pivot2 a b c d nz) u v =
  BP.≃-trans
    (firstNumeratorReconstruct a b c d u v (Inv._⁻¹ (det2 a b c d) nz))
    (BP.≃-trans (BP.*-congʳ (Inv.*-inverseʳ (det2 a b c d) nz))
      (BP.*-identityˡ u))

secondReconstruct : (p : Pivot2) (u v : B.ℝ) →
  B._≃_ (B._+_ (B._*_ (c p) (firstCoordinate p u v))
                   (B._*_ (d p) (secondCoordinate p u v))) v
secondReconstruct (pivot2 a b c d nz) u v =
  BP.≃-trans
    (secondNumeratorReconstruct a b c d u v (Inv._⁻¹ (det2 a b c d) nz))
    (BP.≃-trans (BP.*-congʳ (Inv.*-inverseʳ (det2 a b c d) nz))
      (BP.*-identityˡ v))

-- Actual affine chart parameters (four slopes, two offsets). Each
-- admissible pivot uses the same Cramer reconstruction above.
record Affine6 : Set where
  constructor affine6
  field
    slopeA slopeB slopeC slopeD offsetE offsetF : B.ℝ

record Frame3 : Set where
  constructor frame3
  field
    x y z : B.ℝ

RouteA9 : Set
RouteA9 = Affine6 × Frame3

-- The selected projective quaternion chart q=(1,x,y,z) has an actual
-- strictly positive denominator via the existing native square theorem.
tailNorm : Frame3 → B.ℝ
tailNorm (frame3 x y z) = B._+_ (B._*_ x x)
  (B._+_ (B._*_ y y) (B._*_ z z))

norm : Frame3 → B.ℝ
norm f = B._+_ B.1ℝ (tailNorm f)

tailNonnegative : (f : Frame3) → B.NonNegative (tailNorm f)
tailNonnegative (frame3 x y z) = BP.nonNegx,y⇒nonNegx+y
  (Square.bishopSquareNonnegative x)
  (BP.nonNegx,y⇒nonNegx+y
    (Square.bishopSquareNonnegative y) (Square.bishopSquareNonnegative z))

onePositive : B._<_ B.0ℝ B.1ℝ
onePositive = BP.p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (RatP.positive⁻¹ 1ℚᵘ)

normPositive : (f : Frame3) → B._<_ B.0ℝ (norm f)
normPositive f = BP.<-≤-trans onePositive
  (BP.≤-respˡ-≃ (BP.≃-symm (BP.+-identityʳ B.1ℝ))
    (BP.+-monoʳ-≤ B.1ℝ (BP.nonNegx⇒0≤x (tailNonnegative f))))

frameInverse : Frame3 → B.ℝ
frameInverse f = Inv._⁻¹ (norm f) (inj₂ (normPositive f))

frameInverseCancels : (f : Frame3) →
  B._≃_ (B._*_ (frameInverse f) (norm f)) B.1ℝ
frameInverseCancels f = Inv.*-inverseˡ (norm f) (inj₂ (normPositive f))

-- Native Bishop polynomial certificates for the unnormalized quaternion
-- rotation numerator. The norm denominator is not a fresh axiom.
numeratorGram00 : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y y) (B._*_ z z)) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y y) (B._*_ z z)) (B._+_ (B._*_ y y) (B._*_ z z))))) (B._+_ (B._*_ (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z))) (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z)))) (B._*_ (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y))) (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y)))))) (B._*_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))))
numeratorGram00 w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → (((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((y ⊗ y) ⊕ (z ⊗ z)) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((y ⊗ y) ⊕ (z ⊗ z)) ⊕ ((y ⊗ y) ⊕ (z ⊗ z))))) ⊕ (((((x ⊗ y) ⊕ (w ⊗ z)) ⊕ ((x ⊗ y) ⊕ (w ⊗ z))) ⊗ (((x ⊗ y) ⊕ (w ⊗ z)) ⊕ ((x ⊗ y) ⊕ (w ⊗ z)))) ⊕ ((((x ⊗ z) ⊖ (w ⊗ y)) ⊕ ((x ⊗ z) ⊖ (w ⊗ y))) ⊗ (((x ⊗ z) ⊖ (w ⊗ y)) ⊕ ((x ⊗ z) ⊖ (w ⊗ y)))))) ⊜ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ ((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z))))))
    BP.≃-refl w x y z

numeratorGram01 : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y y) (B._*_ z z)) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._-_ (B._*_ x y) (B._*_ w z)) (B._-_ (B._*_ x y) (B._*_ w z)))) (B._+_ (B._*_ (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z))))) (B._*_ (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y))) (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x)))))) B.0ℝ
numeratorGram01 w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → (((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((y ⊗ y) ⊕ (z ⊗ z)) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ (((x ⊗ y) ⊖ (w ⊗ z)) ⊕ ((x ⊗ y) ⊖ (w ⊗ z)))) ⊕ (((((x ⊗ y) ⊕ (w ⊗ z)) ⊕ ((x ⊗ y) ⊕ (w ⊗ z))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (z ⊗ z)) ⊕ ((x ⊗ x) ⊕ (z ⊗ z))))) ⊕ ((((x ⊗ z) ⊖ (w ⊗ y)) ⊕ ((x ⊗ z) ⊖ (w ⊗ y))) ⊗ (((y ⊗ z) ⊕ (w ⊗ x)) ⊕ ((y ⊗ z) ⊕ (w ⊗ x)))))) ⊜ Κ 0ℚᵘ)
    BP.≃-refl w x y z

numeratorGram02 : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y y) (B._*_ z z)) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x z) (B._*_ w y)) (B._+_ (B._*_ x z) (B._*_ w y)))) (B._+_ (B._*_ (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z))) (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x)))) (B._*_ (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y))))))) B.0ℝ
numeratorGram02 w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → (((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((y ⊗ y) ⊕ (z ⊗ z)) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ (((x ⊗ z) ⊕ (w ⊗ y)) ⊕ ((x ⊗ z) ⊕ (w ⊗ y)))) ⊕ (((((x ⊗ y) ⊕ (w ⊗ z)) ⊕ ((x ⊗ y) ⊕ (w ⊗ z))) ⊗ (((y ⊗ z) ⊖ (w ⊗ x)) ⊕ ((y ⊗ z) ⊖ (w ⊗ x)))) ⊕ ((((x ⊗ z) ⊖ (w ⊗ y)) ⊕ ((x ⊗ z) ⊖ (w ⊗ y))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ x) ⊕ (y ⊗ y))))))) ⊜ Κ 0ℚᵘ)
    BP.≃-refl w x y z

numeratorGram11 : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._+_ (B._-_ (B._*_ x y) (B._*_ w z)) (B._-_ (B._*_ x y) (B._*_ w z))) (B._+_ (B._-_ (B._*_ x y) (B._*_ w z)) (B._-_ (B._*_ x y) (B._*_ w z)))) (B._+_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z)))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z))))) (B._*_ (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x))) (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x)))))) (B._*_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))))
numeratorGram11 w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → (((((x ⊗ y) ⊖ (w ⊗ z)) ⊕ ((x ⊗ y) ⊖ (w ⊗ z))) ⊗ (((x ⊗ y) ⊖ (w ⊗ z)) ⊕ ((x ⊗ y) ⊖ (w ⊗ z)))) ⊕ (((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (z ⊗ z)) ⊕ ((x ⊗ x) ⊕ (z ⊗ z)))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (z ⊗ z)) ⊕ ((x ⊗ x) ⊕ (z ⊗ z))))) ⊕ ((((y ⊗ z) ⊕ (w ⊗ x)) ⊕ ((y ⊗ z) ⊕ (w ⊗ x))) ⊗ (((y ⊗ z) ⊕ (w ⊗ x)) ⊕ ((y ⊗ z) ⊕ (w ⊗ x)))))) ⊜ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ ((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z))))))
    BP.≃-refl w x y z

numeratorGram12 : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._+_ (B._-_ (B._*_ x y) (B._*_ w z)) (B._-_ (B._*_ x y) (B._*_ w z))) (B._+_ (B._+_ (B._*_ x z) (B._*_ w y)) (B._+_ (B._*_ x z) (B._*_ w y)))) (B._+_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z)))) (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x)))) (B._*_ (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y))))))) B.0ℝ
numeratorGram12 w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → (((((x ⊗ y) ⊖ (w ⊗ z)) ⊕ ((x ⊗ y) ⊖ (w ⊗ z))) ⊗ (((x ⊗ z) ⊕ (w ⊗ y)) ⊕ ((x ⊗ z) ⊕ (w ⊗ y)))) ⊕ (((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (z ⊗ z)) ⊕ ((x ⊗ x) ⊕ (z ⊗ z)))) ⊗ (((y ⊗ z) ⊖ (w ⊗ x)) ⊕ ((y ⊗ z) ⊖ (w ⊗ x)))) ⊕ ((((y ⊗ z) ⊕ (w ⊗ x)) ⊕ ((y ⊗ z) ⊕ (w ⊗ x))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ x) ⊕ (y ⊗ y))))))) ⊜ Κ 0ℚᵘ)
    BP.≃-refl w x y z

numeratorGram22 : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._+_ (B._+_ (B._*_ x z) (B._*_ w y)) (B._+_ (B._*_ x z) (B._*_ w y))) (B._+_ (B._+_ (B._*_ x z) (B._*_ w y)) (B._+_ (B._*_ x z) (B._*_ w y)))) (B._+_ (B._*_ (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x))) (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x)))) (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y)))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y))))))) (B._*_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))))
numeratorGram22 w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → (((((x ⊗ z) ⊕ (w ⊗ y)) ⊕ ((x ⊗ z) ⊕ (w ⊗ y))) ⊗ (((x ⊗ z) ⊕ (w ⊗ y)) ⊕ ((x ⊗ z) ⊕ (w ⊗ y)))) ⊕ (((((y ⊗ z) ⊖ (w ⊗ x)) ⊕ ((y ⊗ z) ⊖ (w ⊗ x))) ⊗ (((y ⊗ z) ⊖ (w ⊗ x)) ⊕ ((y ⊗ z) ⊖ (w ⊗ x)))) ⊕ ((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ x) ⊕ (y ⊗ y)))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ x) ⊕ (y ⊗ y))))))) ⊜ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ ((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z))))))
    BP.≃-refl w x y z

numeratorDeterminant : (w x y z : B.ℝ) → B._≃_ (B._+_ (B._-_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y y) (B._*_ z z)) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._-_ (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z)))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y))))) (B._*_ (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x))) (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x)))))) (B._*_ (B._+_ (B._-_ (B._*_ x y) (B._*_ w z)) (B._-_ (B._*_ x y) (B._*_ w z))) (B._-_ (B._*_ (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y))))) (B._*_ (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x))) (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y))))))) (B._*_ (B._+_ (B._+_ (B._*_ x z) (B._*_ w y)) (B._+_ (B._*_ x z) (B._*_ w y))) (B._-_ (B._*_ (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z))) (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x)))) (B._*_ (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z)))) (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y))))))) (B._*_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._*_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z))))))
numeratorDeterminant w x y z =
  let open BP.ℝ-Solver in
  solve 4 (λ w x y z → ((((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((y ⊗ y) ⊕ (z ⊗ z)) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ (((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (z ⊗ z)) ⊕ ((x ⊗ x) ⊕ (z ⊗ z)))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ x) ⊕ (y ⊗ y))))) ⊖ ((((y ⊗ z) ⊖ (w ⊗ x)) ⊕ ((y ⊗ z) ⊖ (w ⊗ x))) ⊗ (((y ⊗ z) ⊕ (w ⊗ x)) ⊕ ((y ⊗ z) ⊕ (w ⊗ x)))))) ⊖ ((((x ⊗ y) ⊖ (w ⊗ z)) ⊕ ((x ⊗ y) ⊖ (w ⊗ z))) ⊗ (((((x ⊗ y) ⊕ (w ⊗ z)) ⊕ ((x ⊗ y) ⊕ (w ⊗ z))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ x) ⊕ (y ⊗ y))))) ⊖ ((((y ⊗ z) ⊖ (w ⊗ x)) ⊕ ((y ⊗ z) ⊖ (w ⊗ x))) ⊗ (((x ⊗ z) ⊖ (w ⊗ y)) ⊕ ((x ⊗ z) ⊖ (w ⊗ y))))))) ⊕ ((((x ⊗ z) ⊕ (w ⊗ y)) ⊕ ((x ⊗ z) ⊕ (w ⊗ y))) ⊗ (((((x ⊗ y) ⊕ (w ⊗ z)) ⊕ ((x ⊗ y) ⊕ (w ⊗ z))) ⊗ (((y ⊗ z) ⊕ (w ⊗ x)) ⊕ ((y ⊗ z) ⊕ (w ⊗ x)))) ⊖ ((((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊖ (((x ⊗ x) ⊕ (z ⊗ z)) ⊕ ((x ⊗ x) ⊕ (z ⊗ z)))) ⊗ (((x ⊗ z) ⊖ (w ⊗ y)) ⊕ ((x ⊗ z) ⊖ (w ⊗ y))))))) ⊜ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ (((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))) ⊗ ((w ⊗ w) ⊕ ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z)))))))
    BP.≃-refl w x y z

-- These establish the polynomial Gram and determinant identities for
-- arbitrary Bishop components. Normalized SO3 matrix and its full
-- projective inverse / setoid chart transport are separate source welds.
-- Do not coerce B._≃_ to Agda propositional equality for Chart.


-- Actual normalized matrix on the original Bishop reals. A nonzero ray
-- is admitted only with constructive apartness of its norm square.
record Vec3 : Set where
  constructor vec3
  field v0 v1 v2 : B.ℝ
open Vec3 public

record Matrix3 : Set where
  constructor matrix3
  field col0 col1 col2 : Vec3
open Matrix3 public

column0 column1 column2 : Matrix3 → Vec3
column0 = col0
column1 = col1
column2 = col2

dot3 : Vec3 → Vec3 → B.ℝ
dot3 (vec3 a b c) (vec3 d e f) =
  B._+_ (B._*_ a d) (B._+_ (B._*_ b e) (B._*_ c f))

scale3 : B.ℝ → Vec3 → Vec3
scale3 i (vec3 a b c) = vec3 (B._*_ i a) (B._*_ i b) (B._*_ i c)

scaleMatrix : B.ℝ → Matrix3 → Matrix3
scaleMatrix i (matrix3 a b c) = matrix3 (scale3 i a) (scale3 i b) (scale3 i c)

norm4 : B.ℝ → B.ℝ → B.ℝ → B.ℝ → B.ℝ
norm4 w x y z = (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z))))

numerator : B.ℝ → B.ℝ → B.ℝ → B.ℝ → Matrix3
numerator w x y z = matrix3
  (vec3 (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y y) (B._*_ z z)) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x y) (B._*_ w z)) (B._+_ (B._*_ x y) (B._*_ w z))) (B._+_ (B._-_ (B._*_ x z) (B._*_ w y)) (B._-_ (B._*_ x z) (B._*_ w y))))
  (vec3 (B._+_ (B._-_ (B._*_ x y) (B._*_ w z)) (B._-_ (B._*_ x y) (B._*_ w z))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ z z)) (B._+_ (B._*_ x x) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ y z) (B._*_ w x)) (B._+_ (B._*_ y z) (B._*_ w x))))
  (vec3 (B._+_ (B._+_ (B._*_ x z) (B._*_ w y)) (B._+_ (B._*_ x z) (B._*_ w y))) (B._+_ (B._-_ (B._*_ y z) (B._*_ w x)) (B._-_ (B._*_ y z) (B._*_ w x))) (B._-_ (B._+_ (B._*_ w w) (B._+_ (B._*_ x x) (B._+_ (B._*_ y y) (B._*_ z z)))) (B._+_ (B._+_ (B._*_ x x) (B._*_ y y)) (B._+_ (B._*_ x x) (B._*_ y y)))))

rotation : (w x y z : B.ℝ) → B._≄0 (norm4 w x y z) → Matrix3
rotation w x y z nz =
  scaleMatrix (Inv._⁻¹ (norm4 w x y z) nz) (numerator w x y z)

normLeadingOne : (f : Frame3) →
  B._≃_ (norm4 B.1ℝ (Frame3.x f) (Frame3.y f) (Frame3.z f)) (norm f)
normLeadingOne (frame3 x y z) =
  BP.+-cong (BP.*-identityˡ B.1ℝ) BP.≃-refl

leadingOneApart : (f : Frame3) →
  B._≄0 (norm4 B.1ℝ (Frame3.x f) (Frame3.y f) (Frame3.z f))
leadingOneApart f = inj₂ (BP.<-respʳ-≃ (BP.≃-sym (normLeadingOne f)) (normPositive f))

frameRotation : Frame3 → Matrix3
frameRotation f = rotation B.1ℝ (Frame3.x f) (Frame3.y f) (Frame3.z f) (leadingOneApart f)

gramScaleScalar : (i a b c d e f : B.ℝ) → B._≃_ (B._+_ (B._*_ (B._*_ i a) (B._*_ i d)) (B._+_ (B._*_ (B._*_ i b) (B._*_ i e)) (B._*_ (B._*_ i c) (B._*_ i f)))) (B._*_ (B._*_ i i) (B._+_ (B._*_ a d) (B._+_ (B._*_ b e) (B._*_ c f))))
gramScaleScalar i a b c d e f =
  let open BP.ℝ-Solver in
  solve 7 (λ i a b c d e f → (((i ⊗ a) ⊗ (i ⊗ d)) ⊕ (((i ⊗ b) ⊗ (i ⊗ e)) ⊕ ((i ⊗ c) ⊗ (i ⊗ f)))) ⊜ ((i ⊗ i) ⊗ ((a ⊗ d) ⊕ ((b ⊗ e) ⊕ (c ⊗ f)))))
    BP.≃-refl i a b c d e f

dotScale : (i : B.ℝ) (u v : Vec3) →
  B._≃_ (dot3 (scale3 i u) (scale3 i v)) (B._*_ (B._*_ i i) (dot3 u v))
dotScale i (vec3 a b c) (vec3 d e f) = gramScaleScalar i a b c d e f

rotationGram00 : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (dot3 (column0 (rotation w x y z nz)) (column0 (rotation w x y z nz))) B.1ℝ
rotationGram00 w x y z nz =
  BP.≃-trans (dotScale (Inv._⁻¹ (norm4 w x y z) nz)
    (column0 (numerator w x y z)) (column0 (numerator w x y z)))
    (BP.≃-trans (BP.*-congˡ (numeratorGram00 w x y z))
      (Rec.inverseSquareCancelsSquare (norm4 w x y z) nz))

rotationGram01 : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (dot3 (column0 (rotation w x y z nz)) (column1 (rotation w x y z nz))) B.0ℝ
rotationGram01 w x y z nz =
  BP.≃-trans (dotScale (Inv._⁻¹ (norm4 w x y z) nz)
    (column0 (numerator w x y z)) (column1 (numerator w x y z)))
    (BP.≃-trans (BP.*-congˡ (numeratorGram01 w x y z))
      (BP.*-zeroʳ (Rec.inverseSquare (norm4 w x y z) nz)))

rotationGram02 : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (dot3 (column0 (rotation w x y z nz)) (column2 (rotation w x y z nz))) B.0ℝ
rotationGram02 w x y z nz =
  BP.≃-trans (dotScale (Inv._⁻¹ (norm4 w x y z) nz)
    (column0 (numerator w x y z)) (column2 (numerator w x y z)))
    (BP.≃-trans (BP.*-congˡ (numeratorGram02 w x y z))
      (BP.*-zeroʳ (Rec.inverseSquare (norm4 w x y z) nz)))

rotationGram11 : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (dot3 (column1 (rotation w x y z nz)) (column1 (rotation w x y z nz))) B.1ℝ
rotationGram11 w x y z nz =
  BP.≃-trans (dotScale (Inv._⁻¹ (norm4 w x y z) nz)
    (column1 (numerator w x y z)) (column1 (numerator w x y z)))
    (BP.≃-trans (BP.*-congˡ (numeratorGram11 w x y z))
      (Rec.inverseSquareCancelsSquare (norm4 w x y z) nz))

rotationGram12 : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (dot3 (column1 (rotation w x y z nz)) (column2 (rotation w x y z nz))) B.0ℝ
rotationGram12 w x y z nz =
  BP.≃-trans (dotScale (Inv._⁻¹ (norm4 w x y z) nz)
    (column1 (numerator w x y z)) (column2 (numerator w x y z)))
    (BP.≃-trans (BP.*-congˡ (numeratorGram12 w x y z))
      (BP.*-zeroʳ (Rec.inverseSquare (norm4 w x y z) nz)))

rotationGram22 : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (dot3 (column2 (rotation w x y z nz)) (column2 (rotation w x y z nz))) B.1ℝ
rotationGram22 w x y z nz =
  BP.≃-trans (dotScale (Inv._⁻¹ (norm4 w x y z) nz)
    (column2 (numerator w x y z)) (column2 (numerator w x y z)))
    (BP.≃-trans (BP.*-congˡ (numeratorGram22 w x y z))
      (Rec.inverseSquareCancelsSquare (norm4 w x y z) nz))

-- determinant is defined on columns of the SAME matrix above.
det3 : Matrix3 → B.ℝ
det3 (matrix3 (vec3 a d g) (vec3 b e h) (vec3 c f j)) =
  (B._+_ (B._-_ (B._*_ a (B._-_ (B._*_ e j) (B._*_ f h))) (B._*_ b (B._-_ (B._*_ d j) (B._*_ f g)))) (B._*_ c (B._-_ (B._*_ d h) (B._*_ e g))))

detScaleScalar : (i a b c d e f g h j : B.ℝ) → B._≃_ (B._+_ (B._-_ (B._*_ (B._*_ i a) (B._-_ (B._*_ (B._*_ i e) (B._*_ i j)) (B._*_ (B._*_ i f) (B._*_ i h)))) (B._*_ (B._*_ i b) (B._-_ (B._*_ (B._*_ i d) (B._*_ i j)) (B._*_ (B._*_ i f) (B._*_ i g))))) (B._*_ (B._*_ i c) (B._-_ (B._*_ (B._*_ i d) (B._*_ i h)) (B._*_ (B._*_ i e) (B._*_ i g))))) (B._*_ (B._*_ i (B._*_ i i)) (B._+_ (B._-_ (B._*_ a (B._-_ (B._*_ e j) (B._*_ f h))) (B._*_ b (B._-_ (B._*_ d j) (B._*_ f g)))) (B._*_ c (B._-_ (B._*_ d h) (B._*_ e g)))))
detScaleScalar i a b c d e f g h j =
  let open BP.ℝ-Solver in
  solve 10 (λ i a b c d e f g h j → ((((i ⊗ a) ⊗ (((i ⊗ e) ⊗ (i ⊗ j)) ⊖ ((i ⊗ f) ⊗ (i ⊗ h)))) ⊖ ((i ⊗ b) ⊗ (((i ⊗ d) ⊗ (i ⊗ j)) ⊖ ((i ⊗ f) ⊗ (i ⊗ g))))) ⊕ ((i ⊗ c) ⊗ (((i ⊗ d) ⊗ (i ⊗ h)) ⊖ ((i ⊗ e) ⊗ (i ⊗ g))))) ⊜ ((i ⊗ (i ⊗ i)) ⊗ (((a ⊗ ((e ⊗ j) ⊖ (f ⊗ h))) ⊖ (b ⊗ ((d ⊗ j) ⊖ (f ⊗ g)))) ⊕ (c ⊗ ((d ⊗ h) ⊖ (e ⊗ g))))))
    BP.≃-refl i a b c d e f g h j

detScale : (i : B.ℝ) (r : Matrix3) →
  B._≃_ (det3 (scaleMatrix i r)) (B._*_ (B._*_ i (B._*_ i i)) (det3 r))
detScale i (matrix3 (vec3 a d g) (vec3 b e h) (vec3 c f j)) =
  detScaleScalar i a b c d e f g h j

cubeCancelRearrange : (i n : B.ℝ) → B._≃_ (B._*_ (B._*_ i (B._*_ i i)) (B._*_ n (B._*_ n n))) (B._*_ (B._*_ i n) (B._*_ (B._*_ i i) (B._*_ n n)))
cubeCancelRearrange i n =
  let open BP.ℝ-Solver in
  solve 2 (λ i n → ((i ⊗ (i ⊗ i)) ⊗ (n ⊗ (n ⊗ n))) ⊜ ((i ⊗ n) ⊗ ((i ⊗ i) ⊗ (n ⊗ n))))
    BP.≃-refl i n

rotationDetOne : (w x y z : B.ℝ) (nz : B._≄0 (norm4 w x y z)) →
  B._≃_ (det3 (rotation w x y z nz)) B.1ℝ
rotationDetOne w x y z nz =
  let n = norm4 w x y z
      i = Inv._⁻¹ n nz
  in BP.≃-trans (detScale i (numerator w x y z))
    (BP.≃-trans (BP.*-congˡ (numeratorDeterminant w x y z))
      (BP.≃-trans (cubeCancelRearrange i n)
        (BP.≃-trans (BP.*-cong (Inv.*-inverseˡ n nz)
          (Rec.inverseSquareCancelsSquare n nz))
          (BP.*-identityˡ B.1ℝ))))

-- All six upper triangular Gram entries and the determinant now refer
-- to the actual normalized matrix; the reverse entries follow by dot
-- symmetry. Projective inverse and setoid transport remain to attach.
