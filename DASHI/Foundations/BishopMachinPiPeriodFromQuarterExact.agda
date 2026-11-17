module DASHI.Foundations.BishopMachinPiPeriodFromQuarterExact where

------------------------------------------------------------------------
-- ORIGINAL-SOURCE BISHOP PI: quarter-angle -> full period compiler.
--
-- No second pi, no Lean-to-Agda proof import, no fake classical coercion.
-- The source chooses Round11's actual Bishop sine/cosine factorial series
-- and Machin's genuine convergent Bishop real.
--
-- Analytic producer still OPEN: original series Pythagoras and twice-
-- angle identities, plus quarter sin=cos from the rational Machin
-- tangent calculation and branch control.
--
-- This module derives the final period equalities from THOSE OWN SOURCE
-- analytic facts; no asserted period is an input.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as B
import RealProperties as BP
import DASHI.Foundations.BishopMachinPiDoubleAngleAlgebraExact as Algebra
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Cong
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11
import DASHI.Moonshine.JInvariantBishopTrigUnitPhaseExact as UnitPhase

module _ (inputs : Round11.Round11BishopCutset) where

  dataSet : E.BishopElementaryPowerSeriesData
  dataSet = Round11.elementarySeries inputs

  sin cos : B.ℝ → B.ℝ
  sin = E.bishopSin dataSet
  cos = E.bishopCos dataSet

  quarter : B.ℝ
  quarter = Quarter.machinQuarterAngle

  twoQuarter : B.ℝ
  twoQuarter = B._+_ quarter quarter

  fourQuarter : B.ℝ
  fourQuarter = B._+_ twoQuarter twoQuarter

  fourQuarterIsMachinPi :
    B._≃_ fourQuarter Machin.bishopMachinPi
  fourQuarterIsMachinPi =
    BP.≃-trans
      (let open BP.ℝ-Solver in
       solve 1
         (λ t → ((t ⊕ t) ⊕ (t ⊕ t)) ⊜ (Κ (+ 4 / 1) ⊗ t))
         BP.≃-refl quarter)
      Quarter.fourTimesQuarterIsMachinPi

  -- A true source endpoint: these are exactly the missing analytic
  -- lemmas for the selected sin/cos power series and literal theta_M.
  -- No independent pi-period field or arbitrary functions are supplied.
  record MachinQuarterAnalyticInputs : Set where
    field
      sinEqualsCos : B._≃_ (sin quarter) (cos quarter)
      pythagorean : UnitPhase.BishopTrigPythagoreanAt dataSet quarter

      doubleSinAtQuarter :
        B._≃_ (sin twoQuarter)
          (Algebra.doubleSin (sin quarter) (cos quarter))
      doubleCosAtQuarter :
        B._≃_ (cos twoQuarter)
          (Algebra.doubleCos (sin quarter) (cos quarter))
      doubleSinAtTwoQuarter :
        B._≃_ (sin fourQuarter)
          (Algebra.doubleSin (sin twoQuarter) (cos twoQuarter))
      doubleCosAtTwoQuarter :
        B._≃_ (cos fourQuarter)
          (Algebra.doubleCos (sin twoQuarter) (cos twoQuarter))

  open MachinQuarterAnalyticInputs public

  unitSinFirst :
    (w : MachinQuarterAnalyticInputs) →
    B._≃_
      (B._+_
        (Algebra.square (sin quarter))
        (Algebra.square (cos quarter)))
      B.1ℝ
  unitSinFirst w =
    BP.≃-trans
      (BP.+-comm
        (Algebra.square (sin quarter))
        (Algebra.square (cos quarter)))
      (UnitPhase.pythagorean (pythagorean w))

  -- Actual Bishop sine at the actual Bishop Machin real.
  bishopMachinPiSineZero :
    (w : MachinQuarterAnalyticInputs) →
    B._≃_ (sin Machin.bishopMachinPi) B.0ℝ
  bishopMachinPiSineZero w =
    BP.≃-trans
      (BP.≃-symm
        (Cong.bishopSinCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          fourQuarterIsMachinPi))
      (BP.≃-trans
        (doubleSinAtTwoQuarter w)
        (BP.≃-trans
          (BP.*-congʳ (BP.*-cong
            (BP.≃-trans (doubleSinAtQuarter w)
              (Algebra.quarterSinCosEqualityGivesDoubleSinOne
                (sin quarter) (cos quarter)
                (sinEqualsCos w) (unitSinFirst w)))
            (BP.≃-trans (doubleCosAtQuarter w)
              (Algebra.quarterSinCosEqualityGivesDoubleCosZero
                (sin quarter) (cos quarter)
                (sinEqualsCos w)))))
          (Algebra.doubleAngleSinFourZero B.1ℝ B.0ℝ
            BP.≃-refl BP.≃-refl)))

  bishopMachinPiCosineMinusOne :
    (w : MachinQuarterAnalyticInputs) →
    B._≃_ (cos Machin.bishopMachinPi) (B.- B.1ℝ)
  bishopMachinPiCosineMinusOne w =
    BP.≃-trans
      (BP.≃-symm
        (Cong.bishopCosCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          fourQuarterIsMachinPi))
      (BP.≃-trans
        (doubleCosAtTwoQuarter w)
        (BP.≃-trans
          (BP.-cong
            (BP.*-cong
              (BP.≃-trans (doubleCosAtQuarter w)
                (Algebra.quarterSinCosEqualityGivesDoubleCosZero
                  (sin quarter) (cos quarter)
                  (sinEqualsCos w)))
              (BP.≃-trans (doubleCosAtQuarter w)
                (Algebra.quarterSinCosEqualityGivesDoubleCosZero
                  (sin quarter) (cos quarter)
                  (sinEqualsCos w))))
            (BP.*-cong
              (BP.≃-trans (doubleSinAtQuarter w)
                (Algebra.quarterSinCosEqualityGivesDoubleSinOne
                  (sin quarter) (cos quarter)
                  (sinEqualsCos w) (unitSinFirst w)))
              (BP.≃-trans (doubleSinAtQuarter w)
                (Algebra.quarterSinCosEqualityGivesDoubleSinOne
                  (sin quarter) (cos quarter)
                  (sinEqualsCos w) (unitSinFirst w))))))
          (let open BP.ℝ-Solver in
           solve 0
             (((Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1)) ⊖
                (Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1)))
               ⊜ (⊝ Κ (+ 1 / 1)))
             BP.≃-refl)))
