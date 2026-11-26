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
