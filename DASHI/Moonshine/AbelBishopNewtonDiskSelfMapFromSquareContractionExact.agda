module DASHI.Moonshine.AbelBishopNewtonDiskSelfMapFromSquareContractionExact where

------------------------------------------------------------------------
-- REMOVE THE INDEPENDENT NEWTON DISK INVARIANCE HYPOTHESIS.
--
-- Constructive Bishop squared-norm parallelogram estimate:
--   N(a+b) <= 2*(N(a)+N(b)), N(x)=Re(x)^2+Im(x)^2.
--
-- This uses only the original Bishop ordered real ring and the
-- nonnegativity of a square; no sqrt, classical norm, Banach axiom
-- or pointwise complex derivative.
--
-- For c = selected rational Newton center, r = 1/200,
-- lambda = 1/200, first-step K=1/15000:
--
--   2*(lambda^2*r^2 + K^2) = 73/7200000000 < r^2.
--
-- Thus the source squared contraction on the disk and the
-- literal first-step enclosure force the SAME native Newton map
-- to preserve the disk.  The independently parameterized
-- originalNewtonMapsDisk field is no longer an analytic leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
import Data.Rational.Unnormalised.Properties as RationalP
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopSquareNonnegativeExact as Squares
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fractions
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact as Constants
import DASHI.Moonshine.AbelBishopAnalyticNewtonContractionExact as Disk
import DASHI.Moonshine.AbelBishopNewtonLiteralFirstStepFromTaylorExact as Taylor

open Algebra using (_+C_; _-C_)

twoReal : BishopReal.ℝ
twoReal = BishopReal._⋆ (+ 2 / 1)

twoRealNonnegative : BishopReal.NonNegative twoReal
twoRealNonnegative =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (BishopP.p<q⇒p⋆<q⋆
        0ℚᵘ (+ 2 / 1) (RationalP.positive⁻¹ (+ 2 / 1))))

originalBishopNormSquareCongruent :
  ∀ {u v : Complex.BishopComplex} →
  Complex._≈C_ u v →
  BishopReal._≃_ (Norm.normSqC u) (Norm.normSqC v)
originalBishopNormSquareCongruent (realEq , imagEq) =
  BishopP.+-cong
    (BishopP.*-cong realEq realEq)
    (BishopP.*-cong imagEq imagEq)

originalBishopSquaredParallelogramDifference :
  ∀ a b →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._*_ twoReal
        (BishopReal._+_
          (Norm.normSqC a) (Norm.normSqC b)))
      (Norm.normSqC (a +C b)))
    (Norm.normSqC (a -C b))
originalBishopSquaredParallelogramDifference
  (Complex.complex x y) (Complex.complex u v) =
  let open BishopP.ℝ-Solver in
  solve 4
    (λ x′ y′ u′ v′ →
      ((Κ (+ 2 / 1)) ⊗
        (((x′ ⊗ x′) ⊕ (y′ ⊗ y′)) ⊕
          ((u′ ⊗ u′) ⊕ (v′ ⊗ v′))))
      ⊖
        (((x′ ⊕ u′) ⊗ (x′ ⊕ u′)) ⊕
          ((y′ ⊕ v′) ⊗ (y′ ⊕ v′)))
      ⊜
        (((x′ ⊖ u′) ⊗ (x′ ⊖ u′)) ⊕
          ((y′ ⊖ v′) ⊗ (y′ ⊖ v′))))
    BishopP.≃-refl x y u v

originalBishopSquaredTriangleTwo :
  ∀ a b →
  BishopReal._≤_
    (Norm.normSqC (a +C b))
    (BishopReal._*_ twoReal
      (BishopReal._+_ (Norm.normSqC a) (Norm.normSqC b)))
originalBishopSquaredTriangleTwo a b =
  Order.nonnegativeDifferenceGivesOrder
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm
        (originalBishopSquaredParallelogramDifference a b))
      (BishopP.nonNegx⇒0≤x
        (Upper.normSquareNonnegative (a -C b))))

originalBishopNewtonDisplacementDecomposition :
  ∀ T nz z →
  Complex._≈C_
    (Newton.originalBishopNewtonOperator T nz z
      -C Newton.selectedRationalNewtonCenter)
    ((Newton.originalBishopNewtonOperator T nz z
        -C Newton.originalBishopNewtonOperator
          T nz Newton.selectedRationalNewtonCenter)
      +C
      (Newton.originalBishopNewtonOperator
        T nz Newton.selectedRationalNewtonCenter
        -C Newton.selectedRationalNewtonCenter))
originalBishopNewtonDisplacementDecomposition T nz z =
  let
    a = Newton.originalBishopNewtonOperator T nz z
    b = Newton.originalBishopNewtonOperator
      T nz Newton.selectedRationalNewtonCenter
    c = Newton.selectedRationalNewtonCenter
  in
  (let open BishopP.ℝ-Solver in
    solve 3
      (λ a′ b′ c′ →
        a′ ⊖ c′ ⊜
        (a′ ⊖ b′) ⊕ (b′ ⊖ c′))
      BishopP.≃-refl
      (Complex.re a) (Complex.re b) (Complex.re c))
  ,
  (let open BishopP.ℝ-Solver in
    solve 3
      (λ a′ b′ c′ →
        a′ ⊖ c′ ⊜
        (a′ ⊖ b′) ⊕ (b′ ⊖ c′))
      BishopP.≃-refl
      (Complex.im a) (Complex.im b) (Complex.im c))

selectedSquaredInvariantRadiusNumerical :
  BishopReal._≤_
    (BishopReal._*_ twoReal
      (BishopReal._+_
        (BishopReal._*_
          (Norm.square Constants.bishopSelectedNewtonRatio)
          (Norm.square Disk.selectedNewtonRadius))
        (Norm.square Constants.bishopSelectedNewtonIncrementConstant)))
    (Norm.square Disk.selectedNewtonRadius)
selectedSquaredInvariantRadiusNumerical =
  let
    lower : BishopReal.ℝ
    lower = BishopReal._⋆ (+ 73 / 7200000000)
    lowerEq :
      BishopReal._≃_
        (BishopReal._*_ twoReal
          (BishopReal._+_
            (BishopReal._*_
              (Norm.square Constants.bishopSelectedNewtonRatio)
              (Norm.square Disk.selectedNewtonRadius))
            (Norm.square Constants.bishopSelectedNewtonIncrementConstant)))
        lower
    lowerEq =
      let open BishopP.ℝ-Solver in
      solve 0
        ((((Κ (+ 2 / 1)) ⊗
          (((Κ (+ 1 / 200)) ⊗ (Κ (+ 1 / 200))) ⊗
            ((Κ (+ 1 / 200)) ⊗ (Κ (+ 1 / 200)))))
          ⊕ ((Κ (+ 2 / 1)) ⊗
            ((Κ (+ 1 / 15000)) ⊗ (Κ (+ 1 / 15000)))))
          ⊜ Κ (+ 73 / 7200000000))
        BishopP.≃-refl
    upperEq :
      BishopReal._≃_
        (Norm.square Disk.selectedNewtonRadius)
        (BishopReal._⋆ (+ 1 / 40000))
    upperEq =
      let open BishopP.ℝ-Solver in
      solve 0
        ((Κ (+ 1 / 200)) ⊗ (Κ (+ 1 / 200))
          ⊜ Κ (+ 1 / 40000))
        BishopP.≃-refl
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm upperEq)
    (BishopP.≤-respˡ-≃ lowerEq
      (BishopP.p≤q⇒p⋆≤q⋆
        (+ 73 / 7200000000)
        (+ 1 / 40000)
        (Fractions.natFractionLe
          (NatP.≤ᵇ⇒≤ tt))))

originalBishopNewtonDiskInvariantFromSquaredContraction :
  ∀ T nz →
  (contractive : ∀ z w →
    Disk.originalBishopSelectedNewtonDisk z →
    Disk.originalBishopSelectedNewtonDisk w →
    BishopReal._≤_
      (Disk.originalBishopSquaredDistance
        (Newton.originalBishopNewtonOperator T nz z)
        (Newton.originalBishopNewtonOperator T nz w))
      (BishopReal._*_
        (Norm.square Constants.bishopSelectedNewtonRatio)
        (Disk.originalBishopSquaredDistance z w))) →
  (firstStep : BishopReal._≤_
    (Disk.originalBishopNewtonIncrementSquare T nz zero)
    (Norm.square Constants.bishopSelectedNewtonIncrementConstant)) →
  ∀ z →
  Disk.originalBishopSelectedNewtonDisk z →
  Disk.originalBishopSelectedNewtonDisk
    (Newton.originalBishopNewtonOperator T nz z)
originalBishopNewtonDiskInvariantFromSquaredContraction
  T nz contractive firstStep z inside =
  let
    c = Newton.selectedRationalNewtonCenter
    a = Newton.originalBishopNewtonOperator T nz z -C
      Newton.originalBishopNewtonOperator T nz c
    b = Newton.originalBishopNewtonOperator T nz c -C c

    aSqBound :
      BishopReal._≤_
        (Norm.normSqC a)
        (BishopReal._*_
          (Norm.square Constants.bishopSelectedNewtonRatio)
          (Norm.square Disk.selectedNewtonRadius))
    aSqBound =
      BishopP.≤-trans
        (contractive z c inside Disk.originalBishopNewtonCenterInSelectedDisk)
        (BishopP.*-monoˡ-≤-nonNeg
          inside
          (Squares.bishopSquareNonnegative
            Constants.bishopSelectedNewtonRatio))

    bothSqBound :
      BishopReal._≤_
        (BishopReal._+_ (Norm.normSqC a) (Norm.normSqC b))
        (BishopReal._+_
          (BishopReal._*_
            (Norm.square Constants.bishopSelectedNewtonRatio)
            (Norm.square Disk.selectedNewtonRadius))
          (Norm.square Constants.bishopSelectedNewtonIncrementConstant))
    bothSqBound = BishopP.+-mono-≤ aSqBound firstStep

    scaled :
      BishopReal._≤_
        (BishopReal._*_ twoReal
          (BishopReal._+_ (Norm.normSqC a) (Norm.normSqC b)))
        (BishopReal._*_ twoReal
          (BishopReal._+_
            (BishopReal._*_
              (Norm.square Constants.bishopSelectedNewtonRatio)
              (Norm.square Disk.selectedNewtonRadius))
            (Norm.square Constants.bishopSelectedNewtonIncrementConstant)))
    scaled =
      BishopP.*-monoˡ-≤-nonNeg
        bothSqBound twoRealNonnegative
  in
  BishopP.≤-trans
    (BishopP.≤-respˡ-≃
      (originalBishopNormSquareCongruent
        (originalBishopNewtonDisplacementDecomposition T nz z))
      (originalBishopSquaredTriangleTwo a b))
    (BishopP.≤-trans
      scaled
      selectedSquaredInvariantRadiusNumerical)

-- One genuine analytic SOURCE lemma now suffices for the whole
-- original Newton disk contraction package, once the literal Taylor
-- endpoint inequalities have been transported onto Bishop expC.
originalBishopNewtonContractionFromLiteralTaylorAndSquare :
  ∀ T nz →
  (contractive : ∀ z w →
    Disk.originalBishopSelectedNewtonDisk z →
    Disk.originalBishopSelectedNewtonDisk w →
    BishopReal._≤_
      (Disk.originalBishopSquaredDistance
        (Newton.originalBishopNewtonOperator T nz z)
        (Newton.originalBishopNewtonOperator T nz w))
      (BishopReal._*_
        (Norm.square Constants.bishopSelectedNewtonRatio)
        (Disk.originalBishopSquaredDistance z w))) →
  Taylor.OriginalBishopNewtonLiteralTaylorCenterBounds T →
  Disk.OriginalBishopAnalyticNewtonContraction T nz
originalBishopNewtonContractionFromLiteralTaylorAndSquare
  T nz contractive source =
  let
    firstStep =
      Taylor.originalBishopActualTaylorBuildsFirstStepBound
        T nz source
  in
  record
    { Disk.originalNewtonMapsDisk =
        originalBishopNewtonDiskInvariantFromSquaredContraction
          T nz contractive firstStep
    ; Disk.originalNewtonSquaredContraction = contractive
    ; Disk.originalNewtonFirstStepSquared = firstStep
    }
