module DASHI.Foundations.BishopPositiveProductReciprocalSquareExact where

------------------------------------------------------------------------
-- POSITIVE PRODUCT RECIPROCAL-SQUARE NORMALIZATION
--
-- For positive Bishop reals x,y, normalize
--
--   ((x*y)^(-1))^2  ≃  (x^(-1))^2 * (y^(-1))^2.
--
-- The vendored Bishop inverse API exposes the primitive cancellation law
-- `*-inverseˡ`; this owner derives the product rule by uniqueness of a right
-- inverse rather than assuming an undocumented inverse-of-product theorem.
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
open import DASHI.Physics.YangMills.CompactLieProofLevel

positiveNonzero :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x → BishopReal._≄0 x
positiveNonzero = inj₂

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

------------------------------------------------------------------------
-- Inverse uniqueness from the primitive cancellation law.

rightInverseUnique :
  ∀ {value candidate : BishopReal.ℝ} →
  (valueNonzero : BishopReal._≄0 value) →
  BishopReal._≃_
    (BishopReal._*_ candidate value)
    BishopReal.1ℝ →
  BishopReal._≃_
    (Reciprocal.inverse value valueNonzero)
    candidate
rightInverseUnique {value} {candidate} valueNonzero candidateLaw =
  let
    inv = Reciprocal.inverse value valueNonzero
    inverseLaw = BishopInverse.*-inverseˡ value valueNonzero
    valueCandidateLaw :
      BishopReal._≃_
        (BishopReal._*_ value candidate)
        BishopReal.1ℝ
    valueCandidateLaw =
      BishopP.≃-trans
        (BishopP.*-comm value candidate)
        candidateLaw
  in
  BishopP.≃-trans
    (BishopP.≃-symm (BishopP.*-identityʳ inv))
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (BishopP.≃-symm valueCandidateLaw))
      (BishopP.≃-trans
        (BishopP.*-assoc inv value candidate)
        (BishopP.≃-trans
          (BishopP.*-congʳ inverseLaw)
          (BishopP.*-identityˡ candidate))))

------------------------------------------------------------------------
-- Product inverse and reciprocal-square rules for positive factors.

inverseProduct :
  ∀ {x y : BishopReal.ℝ}
    (xPositive : BishopReal._<_ BishopReal.0ℝ x)
    (yPositive : BishopReal._<_ BishopReal.0ℝ y) →
  let
    xNonzero = positiveNonzero xPositive
    yNonzero = positiveNonzero yPositive
    xyNonzero = positiveNonzero (productPositive xPositive yPositive)
  in
  BishopReal._≃_
    (Reciprocal.inverse (BishopReal._*_ x y) xyNonzero)
    (BishopReal._*_
      (Reciprocal.inverse x xNonzero)
      (Reciprocal.inverse y yNonzero))
inverseProduct {x} {y} xPositive yPositive =
  let
    xNonzero = positiveNonzero xPositive
    yNonzero = positiveNonzero yPositive
    xyNonzero = positiveNonzero (productPositive xPositive yPositive)
    ix = Reciprocal.inverse x xNonzero
    iy = Reciprocal.inverse y yNonzero
    xLaw = BishopInverse.*-inverseˡ x xNonzero
    yLaw = BishopInverse.*-inverseˡ y yNonzero

    candidateLaw :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ ix iy)
          (BishopReal._*_ x y))
        BishopReal.1ℝ
    candidateLaw =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 4
          (λ ix′ iy′ x′ y′ →
            (ix′ ⊗ iy′) ⊗ (x′ ⊗ y′)
            ⊜ (ix′ ⊗ x′) ⊗ (iy′ ⊗ y′))
          BishopP.≃-refl ix iy x y)
        (BishopP.≃-trans
          (BishopP.*-cong xLaw yLaw)
          (BishopP.*-identityˡ BishopReal.1ℝ))
  in
  rightInverseUnique xyNonzero candidateLaw

inverseSquareProduct :
  ∀ {x y : BishopReal.ℝ}
    (xPositive : BishopReal._<_ BishopReal.0ℝ x)
    (yPositive : BishopReal._<_ BishopReal.0ℝ y) →
  let
    xNonzero = positiveNonzero xPositive
    yNonzero = positiveNonzero yPositive
    xyNonzero = positiveNonzero (productPositive xPositive yPositive)
  in
  BishopReal._≃_
    (Reciprocal.inverseSquare (BishopReal._*_ x y) xyNonzero)
    (BishopReal._*_
      (Reciprocal.inverseSquare x xNonzero)
      (Reciprocal.inverseSquare y yNonzero))
inverseSquareProduct {x} {y} xPositive yPositive =
  let
    xNonzero = positiveNonzero xPositive
    yNonzero = positiveNonzero yPositive
    xyNonzero = positiveNonzero (productPositive xPositive yPositive)
    ix = Reciprocal.inverse x xNonzero
    iy = Reciprocal.inverse y yNonzero
    productInverse = inverseProduct xPositive yPositive
  in
  BishopP.≃-trans
    (BishopP.*-cong productInverse productInverse)
    (let open BishopP.ℝ-Solver
     in solve 2
       (λ ix′ iy′ →
         (ix′ ⊗ iy′) ⊗ (ix′ ⊗ iy′)
         ⊜ (ix′ ⊗ ix′) ⊗ (iy′ ⊗ iy′))
       BishopP.≃-refl ix iy)

bishopPositiveProductReciprocalSquareLevel : ProofLevel
bishopPositiveProductReciprocalSquareLevel = machineChecked
