module DASHI.Foundations.BishopInverseSquareProductExact where

------------------------------------------------------------------------
-- INVERSE-SQUARE PRODUCT NORMALIZATION
--
-- For positive Bishop reals x,y, prove constructively
--
--   (x*y)^(-2)  ~=  x^(-2) * y^(-2).
--
-- The vendored inverse API exposes the canonical inverse and its cancellation
-- law, but this owner deliberately does not depend on a named inverse-of-product
-- theorem.  Instead candidates are characterized by cancellation and inverse
-- uniqueness is derived algebraically.  This also yields congruence under the
-- Bishop real setoid, keeping nonzero witnesses out of semantic identity.
------------------------------------------------------------------------

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
open import DASHI.Physics.YangMills.CompactLieProofLevel

inverse :
  (value : BishopReal.ℝ) → BishopReal._≄0 value → BishopReal.ℝ
inverse = BishopInverse._⁻¹

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

productPositive :
  ∀ {x y} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ y →
  BishopReal._<_ BishopReal.0ℝ (BishopReal._*_ x y)
productPositive xPositive yPositive =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx xPositive)
      (BishopP.0<x⇒posx yPositive))

productNonzero :
  ∀ {x y} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ y →
  BishopReal._≄0 (BishopReal._*_ x y)
productNonzero xPositive yPositive =
  Reciprocal.xNonzero (productPositive xPositive yPositive)

------------------------------------------------------------------------
-- Any candidate that cancels a nonzero value is setoid-equal to the vendored
-- canonical inverse of that value.

inverseFromCancellation :
  (value candidate : BishopReal.ℝ) →
  (nonzero : BishopReal._≄0 value) →
  BishopReal._≃_
    (BishopReal._*_ candidate value)
    BishopReal.1ℝ →
  BishopReal._≃_ (inverse value nonzero) candidate
inverseFromCancellation value candidate nonzero candidateLaw =
  let
    actual = inverse value nonzero
    actualLaw = BishopInverse.*-inverseˡ value nonzero
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.≃-sym (BishopP.*-identityʳ actual))
    (BishopP.≃-trans
      (BishopP.*-congˡ (BishopP.≃-sym candidateLaw))
      (BishopP.≃-trans
        (solve 3
          (λ a c v → a ⊗ (c ⊗ v) ⊜ c ⊗ (a ⊗ v))
          BishopP.≃-refl actual candidate value)
        (BishopP.≃-trans
          (BishopP.*-congˡ actualLaw)
          (BishopP.*-identityʳ candidate))))

------------------------------------------------------------------------
-- Inverse and reciprocal-square congruence under Bishop setoid equality.

inverseCongruentPositive :
  ∀ {x y} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  (yPositive : BishopReal._<_ BishopReal.0ℝ y) →
  BishopReal._≃_ x y →
  BishopReal._≃_
    (inverse x (Reciprocal.xNonzero xPositive))
    (inverse y (Reciprocal.xNonzero yPositive))
inverseCongruentPositive {x} {y} xPositive yPositive equality =
  inverseFromCancellation
    x
    (inverse y yNonzero)
    xNonzero
    candidateCancels
  where
  xNonzero : BishopReal._≄0 x
  xNonzero = Reciprocal.xNonzero xPositive

  yNonzero : BishopReal._≄0 y
  yNonzero = Reciprocal.xNonzero yPositive

  candidateCancels :
    BishopReal._≃_
      (BishopReal._*_
        (inverse y yNonzero)
        x)
      BishopReal.1ℝ
  candidateCancels =
    BishopP.≃-trans
      (BishopP.*-congˡ equality)
      (BishopInverse.*-inverseˡ y yNonzero)

inverseSquareCongruentPositive :
  ∀ {x y} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  (yPositive : BishopReal._<_ BishopReal.0ℝ y) →
  BishopReal._≃_ x y →
  BishopReal._≃_
    (Reciprocal.inverseSquare x (Reciprocal.xNonzero xPositive))
    (Reciprocal.inverseSquare y (Reciprocal.xNonzero yPositive))
inverseSquareCongruentPositive xPositive yPositive equality =
  BishopP.*-cong
    (inverseCongruentPositive xPositive yPositive equality)
    (inverseCongruentPositive xPositive yPositive equality)

------------------------------------------------------------------------
-- Product inverse by direct cancellation.

inverseProduct :
  ∀ {x y}
    (xPositive : BishopReal._<_ BishopReal.0ℝ x)
    (yPositive : BishopReal._<_ BishopReal.0ℝ y) →
  let
    xNonzero = Reciprocal.xNonzero xPositive
    yNonzero = Reciprocal.xNonzero yPositive
    xyNonzero = productNonzero xPositive yPositive
  in
  BishopReal._≃_
    (inverse (BishopReal._*_ x y) xyNonzero)
    (BishopReal._*_
      (inverse x xNonzero)
      (inverse y yNonzero))
inverseProduct {x} {y} xPositive yPositive =
  inverseFromCancellation
    (BishopReal._*_ x y)
    (BishopReal._*_
      (inverse x xNonzero)
      (inverse y yNonzero))
    xyNonzero
    candidateCancels
  where
  xNonzero : BishopReal._≄0 x
  xNonzero = Reciprocal.xNonzero xPositive

  yNonzero : BishopReal._≄0 y
  yNonzero = Reciprocal.xNonzero yPositive

  xyNonzero : BishopReal._≄0 (BishopReal._*_ x y)
  xyNonzero = productNonzero xPositive yPositive

  candidateCancels :
    BishopReal._≃_
      (BishopReal._*_
        (BishopReal._*_
          (inverse x xNonzero)
          (inverse y yNonzero))
        (BishopReal._*_ x y))
      BishopReal.1ℝ
  candidateCancels =
    let
      xLaw = BishopInverse.*-inverseˡ x xNonzero
      yLaw = BishopInverse.*-inverseˡ y yNonzero
      open BishopP.ℝ-Solver
    in
    BishopP.≃-trans
      (solve 4
        (λ ix iy x′ y′ →
          (ix ⊗ iy) ⊗ (x′ ⊗ y′)
          ⊜ (ix ⊗ x′) ⊗ (iy ⊗ y′))
        BishopP.≃-refl
        (inverse x xNonzero) (inverse y yNonzero) x y)
      (BishopP.≃-trans
        (BishopP.*-cong xLaw yLaw)
        (BishopP.*-identityˡ BishopReal.1ℝ))

------------------------------------------------------------------------
-- Squaring the product-inverse identity yields reciprocal-square splitting.

inverseSquareProduct :
  ∀ {x y}
    (xPositive : BishopReal._<_ BishopReal.0ℝ x)
    (yPositive : BishopReal._<_ BishopReal.0ℝ y) →
  let
    xNonzero = Reciprocal.xNonzero xPositive
    yNonzero = Reciprocal.xNonzero yPositive
    xyNonzero = productNonzero xPositive yPositive
  in
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (BishopReal._*_ x y) xyNonzero)
    (BishopReal._*_
      (Reciprocal.inverseSquare x xNonzero)
      (Reciprocal.inverseSquare y yNonzero))
inverseSquareProduct {x} {y} xPositive yPositive =
  let
    xNonzero = Reciprocal.xNonzero xPositive
    yNonzero = Reciprocal.xNonzero yPositive
    productInverse = inverseProduct xPositive yPositive
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-cong productInverse productInverse)
    (solve 4
      (λ ix iy ix′ iy′ →
        (ix ⊗ iy) ⊗ (ix′ ⊗ iy′)
        ⊜ (ix ⊗ ix′) ⊗ (iy ⊗ iy′))
      BishopP.≃-refl
      (inverse x xNonzero) (inverse y yNonzero)
      (inverse x xNonzero) (inverse y yNonzero))

bishopInverseSquareProductLevel : ProofLevel
bishopInverseSquareProductLevel = machineChecked
