module DASHI.Physics.YangMills.BalabanStrongCouplingBetaRhoSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Tadeusz Balaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Prevent a numerically tempting but mathematically invalid identification.
-- The Shen--Zhu--Zhu parameter |beta| is the inverse-coupling magnitude in the
-- Gibbs action.  DASHI's rho=1/8192 is a selected-background small-field/link
-- radius.  They live in different typed carriers and no theorem identifies
-- them.
--
-- Exact arithmetic is still useful: if rho were substituted merely as a scalar
-- into the four-dimensional SU curvature formula, it lies well inside 1/48
-- and would give normalized margin 509/1024.  This scalar coincidence is not a
-- regime bridge.  A valid bridge must identify the action normalization and
-- the measure family, not merely compare two rational numbers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanStrongCouplingSUFourDimensionalMarginExact as Strong

data StrongCouplingInverseBeta : Set where
  inverseBetaMagnitude : ℚ → StrongCouplingInverseBeta

data SelectedBackgroundRadius : Set where
  selectedRadius : ℚ → SelectedBackgroundRadius

paperInteriorBeta : StrongCouplingInverseBeta
paperInteriorBeta = inverseBetaMagnitude (+ 1 / 96)

dashiSelectedRho : SelectedBackgroundRadius
dashiSelectedRho = selectedRadius (+ 1 / 8192)

rhoScalar : ℚ
rhoScalar = + 1 / 8192

rhoAgainstStrongCouplingThresholdSlack : ℚ
rhoAgainstStrongCouplingThresholdSlack =
  Strong.suFourDimensionalStrongCouplingThreshold - rhoScalar

rhoAgainstThresholdSlackExact :
  rhoAgainstStrongCouplingThresholdSlack ≡ + 509 / 24576
rhoAgainstThresholdSlackExact = solve []

rhoToInteriorBetaScalarRatioExact :
  rhoScalar ≡ (+ 3 / 256) * (+ 1 / 96)
rhoToInteriorBetaScalarRatioExact = solve []

rhoSubstitutedNormalizedMarginExact :
  Strong.suNormalizedBakryEmeryMargin rhoScalar ≡ + 509 / 1024
rhoSubstitutedNormalizedMarginExact = solve []

record StrongCouplingToSelectedBackgroundBridge : Set₁ where
  field
    betaMagnitude : StrongCouplingInverseBeta
    smallFieldRadius : SelectedBackgroundRadius

    sameActionNormalization : Set
    sameFiniteVolumeMeasureFamily : Set
    sameLatticeSpacingConvention : Set
    sameGaugeAndBoundaryConvention : Set

    scalarComparisonControlsActionHessian : Set
    strongCouplingGapTransfersToSelectedBackgroundRoute : Set

-- No canonical inhabitant is supplied.  In particular, the exact scalar
-- inequalities above do not prove any of the bridge fields.
