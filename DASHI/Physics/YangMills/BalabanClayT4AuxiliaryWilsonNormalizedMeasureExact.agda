module DASHI.Physics.YangMills.BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact where

------------------------------------------------------------------------
-- TRUE NORMALIZED BRILLOUIN LEBESGUE VOLUME FOR THE ACTUAL 4^4 GRID.
--
-- Existing source owners:
--   BalabanClayT4GeneratedBrillouinGridExact: x in [-1,1]^4;
--   BalabanClayT4HypercubicOrbitQuadratureWeightsExact: cell dx volume 1/16;
--   BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact: the four
--     actual-source free 1/hat(q)^2 rational endpoint intervals.
--
-- Physical loop convention: q=pi*x, d^4q/(2pi)^4 = d^4x/16.
-- Thus the finite source 240-cell normalizedRegularSum, whose
-- weights 4,6,4,1 add to 15, must STILL be multiplied by 1/16
-- to become a unit-normalized Brillouin integral. Otherwise the
-- four-orbit fold is sixteen times the probability-normalized one.
--
-- This module proves the actual rational endpoint/volume identities
-- (not an integral theorem). To turn them into an integral enclosure,
-- the original physical sine atom must lie in each selected interval,
-- the Jacobian/source momentum convention must agree, and B4
-- invariance must apply to the actual integrand. No new Wilson+ghost
-- +Haar scalar, shifted propagator, Taylor remainder, full beta
-- coefficient, E1 continuum or Clay mass gap is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitQuadratureWeightsExact as Weights
import DASHI.Physics.YangMills.BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact as Free

brillouinUnitVolumeFactor : ℚ
brillouinUnitVolumeFactor = + 1 / 16

-- The original generated cube has volume 16 in the normalized x chart.
-- Multiplication by the physical (2pi)^(-4) Jacobian makes total mass 1.
totalUnitMass : ℚ
totalUnitMass =
  brillouinUnitVolumeFactor * Weights.totalNormalizedVolume

totalUnitMassExact : totalUnitMass ≡ + 1 / 1
totalUnitMassExact =
  trans
    (cong (brillouinUnitVolumeFactor *_)
      Weights.totalNormalizedVolumeIsSixteen)
    Ring.solve-∀

regularUnitMass : ℚ
regularUnitMass =
  brillouinUnitVolumeFactor * Weights.regularNormalizedVolume

regularUnitMassExact : regularUnitMass ≡ + 15 / 16
regularUnitMassExact =
  trans
    (cong (brillouinUnitVolumeFactor *_)
      Weights.regularNormalizedVolumeIsFifteen)
    Ring.solve-∀

infraredUnitMass : ℚ
infraredUnitMass =
  brillouinUnitVolumeFactor * Weights.infraredWeight

infraredUnitMassExact : infraredUnitMass ≡ + 1 / 16
infraredUnitMassExact =
  trans
    (cong (brillouinUnitVolumeFactor *_)
      Weights.infraredWeightIsOne)
    Ring.solve-∀

-- These are the ACTUAL original free propagator endpoint folds, not
-- a synthetic four-number calculator. Their proofs reuse the already
-- source-written 240->4 rational reduction.
regularFreePropagatorUnitLower : ℚ
regularFreePropagatorUnitLower =
  brillouinUnitVolumeFactor * Free.weightedAuxiliaryLower

regularFreePropagatorUnitUpper : ℚ
regularFreePropagatorUnitUpper =
  brillouinUnitVolumeFactor * Free.weightedAuxiliaryUpper

regularFreePropagatorUnitLowerExact :
  regularFreePropagatorUnitLower ≡ + 15 / 256
regularFreePropagatorUnitLowerExact =
  trans
    (cong (brillouinUnitVolumeFactor *_)
      Free.weightedAuxiliaryLowerExact)
    Ring.solve-∀

regularFreePropagatorUnitUpperExact :
  regularFreePropagatorUnitUpper ≡ + 6592 / 22707
regularFreePropagatorUnitUpperExact =
  trans
    (cong (brillouinUnitVolumeFactor *_)
      Free.weightedAuxiliaryUpperExact)
    Ring.solve-∀

-- Source boundary: the above are finite enclosure coefficients, not
-- assertions of integral monotonicity, full-domain propagator finiteness,
-- or four certified physical one-loop quadratures.
