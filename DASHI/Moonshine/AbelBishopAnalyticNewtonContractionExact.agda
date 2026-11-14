module DASHI.Moonshine.AbelBishopAnalyticNewtonContractionExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP COMPLEX NEWTON DISK: HIGH-ALPHA CONTRACTION CUT.
--
-- Exact source:
--   p0=31813/100000 + i 133724/100000
--   T(z)=z-(expC(z)-z)/(expC(p0)-1).
--
-- The physically/mathematically decisive analytic leaves are the
-- ACTUAL norm-square contractivity of this Newton operator ON its
-- selected Bishop disk and its ACTUAL first Newton step enclosure.
-- These fields are explicit and MUST be proved for the original
-- native expC: they are NOT hypotheses about some unrelated map.
--
-- This module genuinely proves:
--   * the selected center is in its own Euclidean disk;
--   * every original Newton iterate remains inside the disk;
--   * the actual squared Newton increments are bounded by
--       ((1/15000)*(1/200)^n)^2 for all Nat n;
--   * both signed original Bishop coordinates satisfy the exact
--       componentwise scaled geometric bounds already consumed by
--       AbelBishopNewtonSelectedLimitExact.
--
-- Uses original Murray/Bishop real ordered-ring inequalities,
-- source normSq and nonnegative square reflection, no nonconstructive
-- Euclidean square-root operation or Banach axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflection
import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geom
import DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact as Constants
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonSelectedLimitExact as NewtonLimit

originalBishopSquaredDistance :
  Complex.BishopComplex →
  Complex.BishopComplex →
  BishopReal.ℝ
originalBishopSquaredDistance z w =
  Norm.normSqC (Algebra._-C_ z w)

selectedNewtonRadius : BishopReal.ℝ
selectedNewtonRadius = BishopReal._⋆ (+ 1 / 200)

originalBishopSelectedNewtonDisk :
  Complex.BishopComplex → Set
originalBishopSelectedNewtonDisk z =
  BishopReal._≤_
    (originalBishopSquaredDistance
      z Newton.selectedRationalNewtonCenter)
    (Norm.square selectedNewtonRadius)

originalBishopSquaredDistanceSelfZero :
  ∀ z →
  BishopReal._≃_ (originalBishopSquaredDistance z z)
    BishopReal.0ℝ
originalBishopSquaredDistanceSelfZero (Complex.complex a b) =
  let open BishopP.ℝ-Solver in
  solve 2
    (λ x y →
      ((x ⊖ x) ⊗ (x ⊖ x))
      ⊕ ((y ⊖ y) ⊗ (y ⊖ y))
      ⊜ Κ 0ℚᵘ)
    BishopP.≃-refl a b

originalBishopNewtonCenterInSelectedDisk :
  originalBishopSelectedNewtonDisk
    Newton.selectedRationalNewtonCenter
originalBishopNewtonCenterInSelectedDisk =
  BishopP.≤-respˡ-≃
    (originalBishopSquaredDistanceSelfZero
      Newton.selectedRationalNewtonCenter)
    (BishopP.nonNegx⇒0≤x
      (SquareNN.bishopSquareNonnegative selectedNewtonRadius))

record OriginalBishopAnalyticNewtonContraction
    (T : Cartesian.BishopSetoidComplexTranscendentals)
    (nz : Reciprocal.BishopComplexNonzero
      (Newton.originalBishopNewtonDenominator T)) : Set₁ where
  field
    -- The true original exponential/reciprocal analytic disk input,
    -- not an opaque contraction on a separate metric carrier.
    originalNewtonMapsDisk :
      ∀ z →
      originalBishopSelectedNewtonDisk z →
      originalBishopSelectedNewtonDisk
        (Newton.originalBishopNewtonOperator T nz z)

    -- The original Euclidean distance-square contraction with
    -- admissible ratio 1/200, a relaxed bound on |T'| < 7/1500.
    originalNewtonSquaredContraction :
      ∀ z w →
      originalBishopSelectedNewtonDisk z →
      originalBishopSelectedNewtonDisk w →
      BishopReal._≤_
        (originalBishopSquaredDistance
          (Newton.originalBishopNewtonOperator T nz z)
          (Newton.originalBishopNewtonOperator T nz w))
        (BishopReal._*_
          (Norm.square Constants.bishopSelectedNewtonRatio)
          (originalBishopSquaredDistance z w))

    -- Actual first step T(p0)-p0, not an arbitrary initial point.
    originalNewtonFirstStepSquared :
      BishopReal._≤_
        (originalBishopSquaredDistance
          (Newton.originalBishopNewtonOrbit T nz (suc zero))
          (Newton.originalBishopNewtonOrbit T nz zero))
        (Norm.square Constants.bishopSelectedNewtonIncrementConstant)

open OriginalBishopAnalyticNewtonContraction public

originalBishopNewtonOrbitStaysInDisk :
  ∀ T nz →
  (certificate : OriginalBishopAnalyticNewtonContraction T nz) →
  ∀ n →
  originalBishopSelectedNewtonDisk
    (Newton.originalBishopNewtonOrbit T nz n)
originalBishopNewtonOrbitStaysInDisk T nz certificate zero =
  originalBishopNewtonCenterInSelectedDisk
originalBishopNewtonOrbitStaysInDisk T nz certificate (suc n) =
  originalNewtonMapsDisk certificate
    (Newton.originalBishopNewtonOrbit T nz n)
    (originalBishopNewtonOrbitStaysInDisk
      T nz certificate n)

originalBishopNewtonIncrementSquare :
  ∀ T nz →
  Nat → BishopReal.ℝ
originalBishopNewtonIncrementSquare T nz n =
  originalBishopSquaredDistance
    (Newton.originalBishopNewtonOrbit T nz (suc n))
    (Newton.originalBishopNewtonOrbit T nz n)

originalBishopNewtonStepSquaredContraction :
  ∀ T nz →
  (certificate : OriginalBishopAnalyticNewtonContraction T nz) →
  ∀ n →
  BishopReal._≤_
    (originalBishopNewtonIncrementSquare T nz (suc n))
    (BishopReal._*_
      (Norm.square Constants.bishopSelectedNewtonRatio)
      (originalBishopNewtonIncrementSquare T nz n))
originalBishopNewtonStepSquaredContraction T nz certificate n =
  originalNewtonSquaredContraction certificate
    (Newton.originalBishopNewtonOrbit T nz (suc n))
    (Newton.originalBishopNewtonOrbit T nz n)
    (originalBishopNewtonOrbitStaysInDisk T nz certificate (suc n))
    (originalBishopNewtonOrbitStaysInDisk T nz certificate n)

originalBishopSelectedNewtonSuccessorSquare :
  ∀ n →
  BishopReal._≃_
    (BishopReal._*_
      (Norm.square Constants.bishopSelectedNewtonRatio)
      (Norm.square
        (Geom.scaledGeometricTerm
          Constants.bishopSelectedNewtonIncrementConstant
          Constants.bishopSelectedNewtonRatio n)))
    (Norm.square
      (Geom.scaledGeometricTerm
        Constants.bishopSelectedNewtonIncrementConstant
        Constants.bishopSelectedNewtonRatio (suc n)))
originalBishopSelectedNewtonSuccessorSquare n =
  let
    r = Constants.bishopSelectedNewtonRatio
    v = Geom.scaledGeometricTerm
      Constants.bishopSelectedNewtonIncrementConstant r n
    successor = Geom.scaledGeometricSuccessor
      Constants.bishopSelectedNewtonIncrementConstant r n
  in
  BishopP.≃-trans
    (let open BishopP.ℝ-Solver in
     solve 2
       (λ ratio value →
         (ratio ⊗ ratio) ⊗ (value ⊗ value)
         ⊜ (ratio ⊗ value) ⊗ (ratio ⊗ value))
       BishopP.≃-refl r v)
    (BishopP.*-cong
      (BishopP.≃-symm successor)
      (BishopP.≃-symm successor))

originalBishopNewtonStepSquaredGeometric :
  ∀ T nz →
  (certificate : OriginalBishopAnalyticNewtonContraction T nz) →
  ∀ n →
  BishopReal._≤_
    (originalBishopNewtonIncrementSquare T nz n)
    (Norm.square
      (Geom.scaledGeometricTerm
        Constants.bishopSelectedNewtonIncrementConstant
        Constants.bishopSelectedNewtonRatio n))
originalBishopNewtonStepSquaredGeometric T nz certificate zero =
  BishopP.≤-respʳ-≃
    (let open BishopP.ℝ-Solver in
     solve 1
       (λ c →
         (c ⊗ c)
         ⊜ ((c ⊗ Κ 1ℚᵘ) ⊗ (c ⊗ Κ 1ℚᵘ)))
       BishopP.≃-refl Constants.bishopSelectedNewtonIncrementConstant)
    (originalNewtonFirstStepSquared certificate)
originalBishopNewtonStepSquaredGeometric T nz certificate (suc n) =
  BishopP.≤-trans
    (originalBishopNewtonStepSquaredContraction T nz certificate n)
    (BishopP.≤-respʳ-≃
      (originalBishopSelectedNewtonSuccessorSquare n)
      (BishopP.*-monoˡ-≤-nonNeg
        (originalBishopNewtonStepSquaredGeometric
          T nz certificate n)
        (SquareNN.bishopSquareNonnegative
          Constants.bishopSelectedNewtonRatio)))

originalBishopNewtonRealStepAbsoluteBound :
  ∀ T nz →
  (certificate : OriginalBishopAnalyticNewtonContraction T nz) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re
      (Algebra._-C_
        (Newton.originalBishopNewtonOrbit T nz (suc n))
        (Newton.originalBishopNewtonOrbit T nz n)) ∣)
    (Geom.scaledGeometricTerm
      Constants.bishopSelectedNewtonIncrementConstant
      Constants.bishopSelectedNewtonRatio n)
originalBishopNewtonRealStepAbsoluteBound T nz certificate n =
  let
    step = Algebra._-C_
      (Newton.originalBishopNewtonOrbit T nz (suc n))
      (Newton.originalBishopNewtonOrbit T nz n)
    stepSqBelow = originalBishopNewtonStepSquaredGeometric
      T nz certificate n
    componentSquareBound =
      BishopP.≤-trans
        (BishopP.≤-respˡ-≃
          (Norm.absoluteSquare (Complex.re step))
          (Norm.componentSquareBelowNormSqReal step))
        stepSqBelow
  in
  Reflection.squareReflectsOnNonnegative
    (BishopP.nonNeg∣x∣ (Complex.re step))
    (Geom.scaledGeometricNonnegative
      Constants.bishopSelectedNewtonGeometricInputs n)
    componentSquareBound

originalBishopNewtonImagStepAbsoluteBound :
  ∀ T nz →
  (certificate : OriginalBishopAnalyticNewtonContraction T nz) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im
      (Algebra._-C_
        (Newton.originalBishopNewtonOrbit T nz (suc n))
        (Newton.originalBishopNewtonOrbit T nz n)) ∣)
    (Geom.scaledGeometricTerm
      Constants.bishopSelectedNewtonIncrementConstant
      Constants.bishopSelectedNewtonRatio n)
originalBishopNewtonImagStepAbsoluteBound T nz certificate n =
  let
    step = Algebra._-C_
      (Newton.originalBishopNewtonOrbit T nz (suc n))
      (Newton.originalBishopNewtonOrbit T nz n)
    stepSqBelow = originalBishopNewtonStepSquaredGeometric
      T nz certificate n
    componentSquareBound =
      BishopP.≤-trans
        (BishopP.≤-respˡ-≃
          (Norm.absoluteSquare (Complex.im step))
          (Norm.componentSquareBelowNormSqImag step))
        stepSqBelow
  in
  Reflection.squareReflectsOnNonnegative
    (BishopP.nonNeg∣x∣ (Complex.im step))
    (Geom.scaledGeometricNonnegative
      Constants.bishopSelectedNewtonGeometricInputs n)
    componentSquareBound

originalBishopAnalyticNewtonBuildsActualStepBounds :
  ∀ T nz →
  OriginalBishopAnalyticNewtonContraction T nz →
  NewtonLimit.OriginalBishopNewtonSelectedStepBounds T nz
originalBishopAnalyticNewtonBuildsActualStepBounds T nz certificate =
  record
    { NewtonLimit.realStepBound =
        originalBishopNewtonRealStepAbsoluteBound T nz certificate
    ; NewtonLimit.imagStepBound =
        originalBishopNewtonImagStepAbsoluteBound T nz certificate
    }
