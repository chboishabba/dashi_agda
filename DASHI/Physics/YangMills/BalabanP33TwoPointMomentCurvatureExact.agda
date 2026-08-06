module DASHI.Physics.YangMills.BalabanP33TwoPointMomentCurvatureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Paulo A. Faria da Veiga and Michael O'Carroll,
-- "On Yang-Mills Stability Bounds and Plaquette Field Generating Function".
-- arXiv DOI: 10.48550/arXiv.2205.07376.
-- Status: arXiv preprint.
--
-- DASHI CONTRIBUTION
-- Give the smallest exact finite curvature/moment regression behind a
-- generating-function second derivative.  For two rational observable values,
--
--   2(x^2+y^2) - (x+y)^2 = (x-y)^2 >= 0.
--
-- Thus the centered two-point second moment is nonnegative.  The module also
-- records the exact zero-defect case.  This finite convexity fact does not
-- produce spatial decay, an inverse Hessian, transfer-matrix gap or mass gap.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative; nonPositive)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

square : ℚ → ℚ
square value = value * value

squareNonnegative : ∀ value → 0ℚ ≤ square value
squareNonnegative value with ℚₚ.≤-total 0ℚ value
... | inj₁ valueNonnegative =
  let
    instance
      valueNN = nonNegative valueNonnegative
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
  in
  ℚₚ.nonNegative⁻¹ (value * value)
... | inj₂ valueNonpositive =
  let
    instance
      valueNP = nonPositive valueNonpositive
      productNN = ℚₚ.nonPos*nonPos⇒nonNeg value value
  in
  ℚₚ.nonNegative⁻¹ (value * value)

twoPointCurvature : ℚ → ℚ → ℚ
twoPointCurvature x y =
  (2 * (square x + square y)) - square (x + y)

twoPointCurvatureIdentity :
  ∀ x y → twoPointCurvature x y ≡ square (x - y)
twoPointCurvatureIdentity x y = solve (x ∷ y ∷ [])

twoPointCurvatureNonnegative :
  ∀ x y → 0ℚ ≤ twoPointCurvature x y
twoPointCurvatureNonnegative x y =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (twoPointCurvatureIdentity x y))
    (squareNonnegative (x - y))

twoPointCurvatureVanishesOnDiagonal :
  ∀ x → twoPointCurvature x x ≡ 0ℚ
twoPointCurvatureVanishesOnDiagonal x = solve (x ∷ [])

record MomentCurvatureBoundary : Set where
  constructor momentCurvatureBoundary
  field
    nonnegativeMomentCurvatureImpliesPositiveHessianFloor : Set
    nonnegativeMomentCurvatureDoesNotImplyPositiveHessianFloor :
      nonnegativeMomentCurvatureImpliesPositiveHessianFloor → Set

    twoPointConvexityImpliesExponentialClustering : Set
    twoPointConvexityDoesNotImplyExponentialClustering :
      twoPointConvexityImpliesExponentialClustering → Set

canonicalMomentCurvatureBoundary : MomentCurvatureBoundary
canonicalMomentCurvatureBoundary =
  momentCurvatureBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
