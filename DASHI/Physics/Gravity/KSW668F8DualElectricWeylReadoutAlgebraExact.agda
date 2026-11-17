{-# OPTIONS --safe #-}
module DASHI.Physics.Gravity.KSW668F8DualElectricWeylReadoutAlgebraExact where

-- Original KSW668 F8 a=t AdS5 readout definitions, algebraic adapter only.
-- Attribution: existing DASHI F8 owners retain original physical model.
-- This proves rational receiver arithmetic, not curvature from a 5D metric,
-- a weak-Israel solution, stability, convergence or physical observation.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

quarter half double : ℚ
quarter = (+ 1) / 4
half = (+ 1) / 2
double = (+ 2) / 1

-- 'scale' is the external 1/t² receiver factor.
readout4 : ℚ → ℚ → ℚ → ℚ
readout4 scale etaeta rr =
  - (quarter * (scale * (etaeta + rr)))

readout5 : ℚ → ℚ → ℚ → ℚ → ℚ
readout5 scale etaeta eta lap =
  - (half * (scale * ((etaeta + (double * eta)) + - lap)))

readoutDifference : ℚ → ℚ → ℚ → ℚ → ℚ
readoutDifference scale eta rr lap =
  half * (scale * ((lap + rr) + - (double * eta)))

-- E5 - 2 E4 = (Delta3 H + H_rr - 2 H_eta)/(2t²).
dualReadoutCancellation :
  (scale etaeta eta rr lap : ℚ) →
  readout5 scale etaeta eta lap
    + - (double * readout4 scale etaeta rr)
  ≡ readoutDifference scale eta rr lap
dualReadoutCancellation scale etaeta eta rr lap =
  Ring.solve-∀ scale etaeta eta rr lap

dualReadoutReconstruction :
  (scale etaeta eta rr lap : ℚ) →
  readout5 scale etaeta eta lap
  ≡ (double * readout4 scale etaeta rr)
      + readoutDifference scale eta rr lap
dualReadoutReconstruction scale etaeta eta rr lap =
  Ring.solve-∀ scale etaeta eta rr lap

data F8CovariantOpenGate : Set where
  missingSameMetricAdS5InducedGeometry : F8CovariantOpenGate
  missingLinearisedWeylElectricContraction : F8CovariantOpenGate
  missingTTGaugeAndIsraelSourceCompatibility : F8CovariantOpenGate
  missingCoupledSSPRK3StabilityAndBothWeylTrace : F8CovariantOpenGate
  missingIndependentRadialNormalTimeConvergence : F8CovariantOpenGate
