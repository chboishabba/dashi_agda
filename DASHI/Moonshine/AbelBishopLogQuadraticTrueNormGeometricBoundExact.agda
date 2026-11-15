module DASHI.Moonshine.AbelBishopLogQuadraticTrueNormGeometricBoundExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG: FINITE SHARP GEOMETRIC NORM BOUND.
--
-- Complete the FINITE part of P1.L without a geometric-estimate axiom.
-- Reuse:
--  - original termwise true |w| squared control,
--  - original finite Bishop complex Minkowski from R4,
--  - the already constructed Step-V Bishop finite geometric
--    supersolution B=(1-r)^(-1).
--
-- For r=sqrt(N(w)) and 0<=r<1:
--
--  ||sum_{k<n} (-1)^(k+1) w^(k+2)/(k+2)||
--     <= (r*r/2) * (1-r)^(-1).
--
-- This is the true-displacement quadratic bound at EVERY FINITE
-- partial sum. The R4 BishopSquareRootCalculus remains an explicit
-- existing input, NOT a fabricated root constructor. To prove the
-- completed ORIGINAL log remainder estimate still requires an
-- order-closed limit theorem, instantiated root calculus, and the
-- selected r<=2/27 upper-disk transport. No UV/Clay claims.
--
-- Source-written, pinned Agda 2.9 kernel admission pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as R4
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact as Half
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormFiniteMajorantExact as Majorant

private
  K = BishopStepV.bishopOrderedSemiringKernel

-- Construct original Bishop power/Step-V power agreement. Their
-- successor recursion multiplications are in opposite orders:
-- original Bishop real pow may append r on the right; Step-V's
-- power constructor puts r on the left. Commutativity pays this.
originalBishopPowerEqualsStepV :
  ∀ ratio n →
  BishopReal._≃_
    (BishopReal.pow ratio n)
    (StepV.power K ratio n)
originalBishopPowerEqualsStepV ratio zero = BishopP.≃-refl
originalBishopPowerEqualsStepV ratio (suc n) =
  BishopP.≃-trans
    (BishopP.*-congʳ (originalBishopPowerEqualsStepV ratio n))
    (BishopP.*-comm (StepV.power K ratio n) ratio)

-- The source term half*r^(n+2) equals the sharp constant
-- (half*r²) times the existing Step-V r^n, without taking a
-- separate geometric source sequence as axiomatic.
originalBishopHalfQuadraticTermAsStepV :
  ∀ radius n →
  BishopReal._≃_
    (BishopReal._*_ Half.bishopHalf
      (BishopReal.pow radius (suc (suc n))))
    (BishopReal._*_
      (BishopReal._*_ Half.bishopHalf (Norm.square radius))
      (StepV.power K radius n))
originalBishopHalfQuadraticTermAsStepV radius n =
  BishopP.≃-trans
    (let open BishopP.ℝ-Solver
     in solve 3
       (λ half r rn →
         half ⊗ ((rn ⊗ r) ⊗ r)
         ⊜ ((half ⊗ (r ⊗ r)) ⊗ rn))
       BishopP.≃-refl
       Half.bishopHalf radius (BishopReal.pow radius n))
    (BishopP.*-congˡ
      (originalBishopPowerEqualsStepV radius n))

-- Original Bishop SeriesOf and the Step-V finite geometric sum
-- are identified by the SAME finite recursion, including n=0.
originalBishopTrueNormMajorantIsScaledStepV :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w n →
  let radius = Majorant.trueBishopRadius roots w
      scale = BishopReal._*_ Half.bishopHalf (Norm.square radius)
  in BishopReal._≃_
    (Majorant.trueBishopQuadraticFiniteMajorant roots w n)
    (BishopReal._*_ scale (StepV.geometricPartialSum K radius n))
originalBishopTrueNormMajorantIsScaledStepV roots w zero =
  BishopP.≃-symm
    (BishopP.*-zeroʳ
      (BishopReal._*_ Half.bishopHalf
        (Norm.square (Majorant.trueBishopRadius roots w))))
originalBishopTrueNormMajorantIsScaledStepV roots w (suc n) =
  let
    radius = Majorant.trueBishopRadius roots w
    scale = BishopReal._*_ Half.bishopHalf (Norm.square radius)
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (originalBishopTrueNormMajorantIsScaledStepV roots w n)
      (originalBishopHalfQuadraticTermAsStepV radius n))
    (BishopP.≃-symm
      (BishopP.*-distribˡ-+ scale
        (StepV.geometricPartialSum K radius n)
        (StepV.power K radius n)))

-- The chosen r is the original sqrt(N(w)), so its positivity follows
-- from the existing native Bishop complex norm-square positivity.
originalBishopTrueNormGeometricInputs :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  BishopReal._<_ (Majorant.trueBishopRadius roots w)
    BishopReal.1ℝ →
  BishopStepV.BishopGeometricRatio
originalBishopTrueNormGeometricInputs roots w belowOne =
  record
    { BishopStepV.ratio = Majorant.trueBishopRadius roots w
    ; BishopStepV.ratioNonnegative =
        BishopP.nonNegx⇒0≤x
          (R4.rootNonnegative roots (Norm.normSqC w)
            (Upper.normSquareNonnegative w))
    ; BishopStepV.ratioBelowOne = belowOne
    }

-- FINITE majorant <= sharp geometric constant, using the
-- pre-existing proven finite Step-V supersolution induction.
originalBishopFiniteTrueNormMajorantBelowGeometric :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  (belowOne :
    BishopReal._<_ (Majorant.trueBishopRadius roots w)
      BishopReal.1ℝ) →
  ∀ n →
  let radius = Majorant.trueBishopRadius roots w
      inputs = originalBishopTrueNormGeometricInputs roots w belowOne
  in BishopReal._≤_
    (Majorant.trueBishopQuadraticFiniteMajorant roots w n)
    (BishopReal._*_
      (BishopReal._*_ Half.bishopHalf (Norm.square radius))
      (BishopStepV.bishopGeometricUniformBound inputs))
originalBishopFiniteTrueNormMajorantBelowGeometric
    roots w belowOne n =
  let
    radius = Majorant.trueBishopRadius roots w
    inputs = originalBishopTrueNormGeometricInputs roots w belowOne
    scale = BishopReal._*_ Half.bishopHalf (Norm.square radius)
    scaleNN =
      BishopP.nonNegx,y⇒nonNegx*y
        Half.bishopHalfNonnegative
        (SquareNN.bishopSquareNonnegative radius)
  in
  BishopP.≤-respˡ-≃
    (originalBishopTrueNormMajorantIsScaledStepV roots w n)
    (BishopP.*-monoˡ-≤-nonNeg
      (StepV.allFinitePartialSumsBounded
        (BishopStepV.bishopFiniteGeometricUniformBound inputs) n)
      scaleNN)

-- FINITE ORIGINAL SOURCE R2 MAJORANT: the first complete sharp
-- geometric estimate against the actual original shifted log terms.
originalBishopQuadraticFiniteTrueNormGeometricBound :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  (belowOne :
    BishopReal._<_ (Majorant.trueBishopRadius roots w)
      BishopReal.1ℝ) →
  ∀ n →
  let radius = Majorant.trueBishopRadius roots w
      inputs = originalBishopTrueNormGeometricInputs roots w belowOne
  in BishopReal._≤_
    (Majorant.trueBishopRadius roots
      (Finite.originalBishopLogQuadraticTailPrefix w n))
    (BishopReal._*_
      (BishopReal._*_ Half.bishopHalf (Norm.square radius))
      (BishopStepV.bishopGeometricUniformBound inputs))
originalBishopQuadraticFiniteTrueNormGeometricBound
    roots w belowOne n =
  BishopP.≤-trans
    (Majorant.originalBishopQuadraticFiniteTrueNormBound roots w n)
    (originalBishopFiniteTrueNormMajorantBelowGeometric
      roots w belowOne n)
