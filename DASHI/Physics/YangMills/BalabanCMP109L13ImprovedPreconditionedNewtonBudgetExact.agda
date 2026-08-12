module DASHI.Physics.YangMills.BalabanCMP109L13ImprovedPreconditionedNewtonBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Update the Newton budget after the source-scale gauge-adjoint repair.
-- The preconditioned two-background derivative variation coefficient retained
-- from the literal equation-(0.12) Schur budget is
--
--       epsilon_13 = 28625 / 16777216.
--
-- The selected block-average+gauge reduced normal now has the proved floor
--
--       gamma_13 = 130991 / 3145728.
--
-- Therefore the exact squared Newton ratio is
--
--       epsilon_13 / gamma_13 = 85875 / 2095856,
--
-- and it lies strictly below 1/16 with rational gap
--
--       1/16 - epsilon_13/gamma_13 = 11279/523964.
--
-- This is arithmetic only; the full nonlinear CMP109 Newton theorem may
-- consume it only after the same-object equation-(0.12) Frechet derivative is
-- identified with the normalized local kernel whose variation supplies
-- epsilon_13.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109L13PreconditionedNewtonBudgetExact as Previous
import DASHI.Physics.YangMills.BalabanPath13PreconditionedSelectedCombinedFloorExact as Floor

improvedNewtonSquaredRatio : ℚ
improvedNewtonSquaredRatio = + 85875 / 2095856

improvedOneSixteenthGap : ℚ
improvedOneSixteenthGap = + 11279 / 523964

improvedRatioExact :
  Previous.preconditionedCombinedVariation
  ≡ improvedNewtonSquaredRatio * Floor.selectedCombinedFloor13
improvedRatioExact = ℚRing.solve []

improvedRatioPlusGapExact :
  improvedNewtonSquaredRatio + improvedOneSixteenthGap
  ≡ Previous.oneSixteenth
improvedRatioPlusGapExact = ℚRing.solve []

cmp109L13ImprovedNewtonBudgetArithmeticLevel : ProofLevel
cmp109L13ImprovedNewtonBudgetArithmeticLevel = machineChecked
