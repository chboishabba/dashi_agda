module DASHI.Physics.YangMills.BalabanCMP109L13PreconditionedNewtonBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Record the exact rational arithmetic created by the 169 row
-- preconditioner.  If the source-faithful normalized Q derivative variation
-- has squared coefficient 1/2^24, multiplying the twelve average rows by 169
-- changes that coefficient to 28561/2^24.  Adding the already proved
-- two-background gauge coefficient 1/2^18 gives
--
--       epsilon_13 = 28625 / 16777216.
--
-- If the migrated selected gauge floor closes at 101/3072 (the rational
-- one-quarter Young estimate from a 1/18 flat floor and 3/1024 defect floor),
-- then
--
--       epsilon_13 / gamma_13 = 85875 / 1654784
--
-- and the exact gap to the squared 1/16 contraction target is
--
--       1/16 - epsilon_13/gamma_13 = 17549/1654784.
--
-- This module deliberately proves the arithmetic only.  The physical theorem
-- must still identify the L=13 gauge adjoint/defect on the same 342732-state
-- carrier before consuming gamma_13.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

sharpNormalizedQVariation : ℚ
sharpNormalizedQVariation = + 1 / 16777216

preconditionerSquare : ℚ
preconditionerSquare = + 28561 / 1

preconditionedQVariation : ℚ
preconditionedQVariation = + 28561 / 16777216

gaugeTwoBackgroundVariation : ℚ
gaugeTwoBackgroundVariation = + 1 / 262144

preconditionedCombinedVariation : ℚ
preconditionedCombinedVariation = + 28625 / 16777216

candidateSelectedGaugeFloor : ℚ
candidateSelectedGaugeFloor = + 101 / 3072

candidateNewtonSquaredRatio : ℚ
candidateNewtonSquaredRatio = + 85875 / 1654784

oneSixteenth : ℚ
oneSixteenth = + 1 / 16

oneSixteenthRatioGap : ℚ
oneSixteenthRatioGap = + 17549 / 1654784

oneSixteenthFloorGap : ℚ
oneSixteenthFloorGap = + 17549 / 50331648

preconditionedQVariationExact :
  preconditionerSquare * sharpNormalizedQVariation
  ≡ preconditionedQVariation
preconditionedQVariationExact = ℚRing.solve []

combinedVariationExact :
  preconditionedQVariation + gaugeTwoBackgroundVariation
  ≡ preconditionedCombinedVariation
combinedVariationExact = ℚRing.solve []

candidateNewtonRatioExact :
  preconditionedCombinedVariation
  ≡ candidateNewtonSquaredRatio * candidateSelectedGaugeFloor
candidateNewtonRatioExact = ℚRing.solve []

oneSixteenthRatioGapExact :
  candidateNewtonSquaredRatio + oneSixteenthRatioGap
  ≡ oneSixteenth
oneSixteenthRatioGapExact = ℚRing.solve []

oneSixteenthFloorGapExact :
  preconditionedCombinedVariation + oneSixteenthFloorGap
  ≡ oneSixteenth * candidateSelectedGaugeFloor
oneSixteenthFloorGapExact = ℚRing.solve []

preconditionedDerivativeBudgetArithmeticLevel : ProofLevel
preconditionedDerivativeBudgetArithmeticLevel = machineChecked

preconditionedNewtonMarginArithmeticLevel : ProofLevel
preconditionedNewtonMarginArithmeticLevel = machineChecked
