module DASHI.Physics.YangMills.BalabanP33GaugeModeRGResidualCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS Regional Conference Series in Mathematics
-- 92, American Mathematical Society, 1997.
-- DOI: 10.1090/cbms/092.
--
-- Tadeusz Balaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Jan Swoboda,
-- "Morse Homology for the Yang--Mills Gradient Flow",
-- Journal de Mathematiques Pures et Appliquees 98 (2012), 160--210.
-- DOI: 10.1016/j.matpur.2012.02.001.
--
-- Volker Bach, Thomas Chen, Jurg Frohlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate two exact structures without identifying them physically:
--
--   * invariant-mode removal is the same finite projector algebra used by the
--     DASHI 54 = 1 + 53 carrier and by mean-zero Fourier prototypes;
--   * retained - feedback + remainder is an additive defect-controlled square,
--     so the RG remainder is precisely the failure of exact semiconjugacy.
--
-- This module does not prove the physical gauge quotient, a connected
-- Laplacian theorem, or the effective-action derivative bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Common.ReducedModeProjectionExact as Reduced
import DASHI.Physics.Common.CoarseDynamicsCommutatorExact as Coarse
import DASHI.Physics.YangMills.BalabanP33EffectiveSchurGapStepExact as Effective

gaugeConstantModeIsRemoved :
  (value : ℚ) →
  Reduced.meanZeroPart (Reduced.pairField value value)
  ≡ Reduced.pairField 0 0
gaugeConstantModeIsRemoved = Reduced.meanZeroPartKillsConstantField

reducedSixByNineModeCount :
  Reduced.totalModes Reduced.sixByNineReducedModeCount
  ≡ Reduced.invariantModes Reduced.sixByNineReducedModeCount
    + Reduced.fluctuationModes Reduced.sixByNineReducedModeCount
reducedSixByNineModeCount = Reduced.sixByNineIsInvariantPlusReduced

effectiveFineState : ℚ → ℚ → ℚ → ℚ × ℚ
effectiveFineState retained feedback remainder =
  retained , (remainder - feedback)

effectiveSchurIsDefectControlledObservation :
  ∀ retained feedback remainder →
  Coarse.observe Coarse.canonicalRationalDefectSquare
    (Coarse.fineStep Coarse.canonicalRationalDefectSquare
      (effectiveFineState retained feedback remainder))
  ≡ Effective.effectiveSchurQuadratic retained feedback remainder
effectiveSchurIsDefectControlledObservation
    retained feedback remainder =
  ℚRing.solve-∀ retained feedback remainder

effectiveResidual : ℚ → ℚ → ℚ
effectiveResidual feedback remainder = remainder - feedback

effectiveResidualVanishesExactlyWhenSquareCommutes :
  ∀ retained feedback remainder →
  effectiveResidual feedback remainder ≡ 0 →
  Coarse.observe Coarse.canonicalRationalDefectSquare
    (Coarse.fineStep Coarse.canonicalRationalDefectSquare
      (effectiveFineState retained feedback remainder))
  ≡ Coarse.coarseStep Coarse.canonicalRationalDefectSquare
      (Coarse.observe Coarse.canonicalRationalDefectSquare
        (effectiveFineState retained feedback remainder))
effectiveResidualVanishesExactlyWhenSquareCommutes
    retained feedback remainder residualZero =
  Coarse.neutralResidualImpliesExactAt
    Coarse.canonicalRationalDefectSquare
    (effectiveFineState retained feedback remainder)
    residualZero
