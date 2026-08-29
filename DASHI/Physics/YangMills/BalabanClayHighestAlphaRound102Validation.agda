{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102Validation where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102PhysicalCutExact as R102

-- Focused kernel root: importing R102 traverses the new A two-sided beta,
-- shooting-terminal, CMP116 first-gradient covariance and weighted quasi-local
-- series tranche.

aTwoSided : ProofLevel
aTwoSided = R102.rowAHistoryUniformTwoSidedPointwiseBetaRound102Level

aTerminal : ProofLevel
aTerminal = R102.rowAShootingFixedPointTerminalCouplingRound102Level

bcTemporal : ProofLevel
bcTemporal = R102.rowBCGradientCovarianceToHeatDoobDebtRound102Level

bcSpatial : ProofLevel
bcSpatial = R102.rowBCGradientCovarianceToWeightedHeatDoobRound102Level

cDyson : ProofLevel
cDyson = R102.rowCPositiveWeightedDysonSeriesRound102Level

countStillFour = R102.round102FrozenResearchCountStillFour
