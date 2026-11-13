module DASHI.Physics.YangMills.BalabanP0FeynmanGaugeRationalPropagatorInverseExact where

-- Actual positive-denominator rational matrix inverse for the selected
-- Feynman-gauge FREE symbol s*delta_{mu,nu}, using the EXISTING
-- positive-reciprocal theorem (not an arbitrary total 1/s).
--
-- Input s>0 must be proved for the actual original Fourier symbol.
-- The prior Wilson/Bishop source supplies this on admitted regular
-- boxes only after the physical same-sine membership weld.
-- This is the FREE inverse identity, NOT the background gauge
-- propagator, a 3/4-gluon vertex, or a physical one-loop integral.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

delta : Eval.AxisIndex → Eval.AxisIndex → ℚ
delta Eval.axis0 Eval.axis0 = 1ℚ
delta Eval.axis0 Eval.axis1 = 0ℚ
delta Eval.axis0 Eval.axis2 = 0ℚ
delta Eval.axis0 Eval.axis3 = 0ℚ
delta Eval.axis1 Eval.axis0 = 0ℚ
delta Eval.axis1 Eval.axis1 = 1ℚ
delta Eval.axis1 Eval.axis2 = 0ℚ
delta Eval.axis1 Eval.axis3 = 0ℚ
delta Eval.axis2 Eval.axis0 = 0ℚ
delta Eval.axis2 Eval.axis1 = 0ℚ
delta Eval.axis2 Eval.axis2 = 1ℚ
delta Eval.axis2 Eval.axis3 = 0ℚ
delta Eval.axis3 Eval.axis0 = 0ℚ
delta Eval.axis3 Eval.axis1 = 0ℚ
delta Eval.axis3 Eval.axis2 = 0ℚ
delta Eval.axis3 Eval.axis3 = 1ℚ

freeGaugeFixedSymbol : ℚ → Eval.AxisIndex → Eval.AxisIndex → ℚ
freeGaugeFixedSymbol s mu nu = s * delta mu nu

freeGreenSymbol :
  (s : ℚ) → 0ℚ < s → Eval.AxisIndex → Eval.AxisIndex → ℚ
freeGreenSymbol s positive mu nu =
  delta mu nu * Quotient.positiveReciprocal s positive

fourComponentComposition :
  (s r : ℚ) → Eval.AxisIndex → Eval.AxisIndex → ℚ
fourComponentComposition s r mu rho =
  ((s * delta mu Eval.axis0) * (delta Eval.axis0 rho * r))
  + ((s * delta mu Eval.axis1) * (delta Eval.axis1 rho * r))
  + ((s * delta mu Eval.axis2) * (delta Eval.axis2 rho * r))
  + ((s * delta mu Eval.axis3) * (delta Eval.axis3 rho * r))

-- Exact indexed finite-matrix multiplication for arbitrary rational
-- s and r; no physical source premise or denominator division yet.
diagonalCompositionExact :
  ∀ s r mu rho →
  fourComponentComposition s r mu rho ≡ (s * r) * delta mu rho
diagonalCompositionExact s r Eval.axis0 Eval.axis0 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis0 Eval.axis1 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis0 Eval.axis2 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis0 Eval.axis3 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis1 Eval.axis0 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis1 Eval.axis1 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis1 Eval.axis2 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis1 Eval.axis3 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis2 Eval.axis0 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis2 Eval.axis1 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis2 Eval.axis2 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis2 Eval.axis3 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis3 Eval.axis0 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis3 Eval.axis1 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis3 Eval.axis2 = Ring.solve-∀ s r
diagonalCompositionExact s r Eval.axis3 Eval.axis3 = Ring.solve-∀ s r

-- This is a genuine 4×4 inverse, with the original proof
-- `positiveReciprocalRightInverse` paying the only division.
feynmanFreeGreenIsInverse :
  ∀ s (positive : 0ℚ < s) mu rho →
  fourComponentComposition s (Quotient.positiveReciprocal s positive) mu rho
    ≡ delta mu rho
feynmanFreeGreenIsInverse s positive mu rho =
  trans
    (diagonalCompositionExact s
      (Quotient.positiveReciprocal s positive) mu rho)
    (trans
      (cong (λ t → t * delta mu rho)
        (Quotient.positiveReciprocalRightInverse s positive))
      (ℚP.*-identityˡ (delta mu rho)))

-- This does not automatically invert the singular infrared mode s=0.
-- The original positive-only quotient proof enforces that distinction.
