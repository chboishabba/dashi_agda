module DASHI.Physics.YangMills.BalabanClayGate4LightweightValidation where

------------------------------------------------------------------------
-- Lightweight Gate-4 validation root.
--
-- This intentionally imports only the P06/P07/P08/P09 theorem-surface audit,
-- the exact physical RG handoff, the rational common-budget theorem, and the
-- rooted R-operation -> entropy shell -> shared-slack bridge.  It does not
-- import BalabanPolymerDiameterEntropy, SFGC, or the triadic Closure graph.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropyLight as Polymer
import DASHI.Physics.YangMills.BalabanClayGate4LightweightPolymerRGHandoffExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4LightweightOneStepRegionExact as OneStep
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as RShell
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF
import DASHI.Physics.YangMills.BalabanYM4LargeFieldCoupledStepExact as LFCoupled
import DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact as Eq1100
import DASHI.Physics.YangMills.BalabanCMP122Equation1100EntropyBudgetExact as EqEntropy
import DASHI.Physics.YangMills.BalabanCMP122Equation1100SharedSlackExact as EqSlack

polymerAuditReady = Polymer.lightweightPolymerAuditReady
polymerAuditNoPromotion = Polymer.lightweightPolymerAuditNoPromotion

polymerRGHandoffLevel = Gate4.lightweightPolymerAuditRGHandoffLevel
physicalOneStepAssemblyLevel = Gate4.lightweightOneStepRGAssemblyLevel
allScaleRGAssemblyLevel = Gate4.lightweightAllScaleRGAssemblyLevel

coupledOneStepInvariantRegionLevel = OneStep.lightweightGate4OneStepRegionLevel

-- High-alpha large-field bridge:
--   CMP122 (1.100)
--     -> weighted pointwise R decay
--     -> rooted entropy spends the residual diameter decay
--     -> shell <= exp(-p0(g_k)) 2^{-n}
--     -> finite large-field contribution <= 2 exp(-p0(g_k))
--     -> source-level shared one-step slack
--     -> invariant-region closure.
cmp122Equation1100PrimarySourceLevel = Eq1100.cmp122Equation1100PrimarySourceLevel
cmp119Equation231ArbitraryDecayReserveLevel =
  Eq1100.cmp119Equation231ArbitraryDecayReserveLevel
cmp122Equation1100EntropyAssemblyLevel =
  EqEntropy.cmp122Equation1100EntropyAssemblyLevel
cmp122Equation1100FiniteContributionLevel =
  EqSlack.cmp122Equation1100FiniteContributionLevel
cmp122Equation1100SharedSlackAssemblyLevel =
  EqSlack.cmp122Equation1100SharedSlackAssemblyLevel

rOperationFiniteEntropyShellAssemblyLevel =
  RShell.rOperationFiniteEntropyShellAssemblyLevel
largeFieldRootedSummationLevel = LF.largeFieldRootedSummationLevel
largeFieldSharedSlackAssemblyLevel = LF.largeFieldSharedSlackAssemblyLevel
largeFieldToSharedRGErrorLevel = LFCoupled.largeFieldToSharedRGErrorLevel
largeFieldCoupledRegionClosureLevel = LFCoupled.largeFieldCoupledRegionClosureLevel

-- Fail-closed physical frontier.  Equation (1.100) itself is now primary-source
-- authority rather than a generic conditional target.  What remains in this
-- segment is the repository representation/weight split, same-geometry rooted
-- entropy payment, identification of the combined R-sector norm contribution,
-- and the concrete numerical shared-slack inequality.  Coupling,
-- boundary-domain, covariance/locality and initial UV inputs remain separate.
cmp122Equation1100RepositoryRepresentationLevel =
  Eq1100.cmp122Equation1100RepositoryRepresentationLevel
cmp122Equation1100WeightSplitIdentificationLevel =
  EqEntropy.cmp122Equation1100WeightSplitIdentificationLevel
cmp119RootedEntropyConsumesResidualDecayLevel =
  EqEntropy.cmp119RootedEntropyConsumesResidualDecayLevel
cmp122CombinedNormContributionIdentificationLevel =
  EqSlack.cmp122CombinedNormContributionIdentificationLevel
cmp122NumericalSharedSlackLevel =
  EqSlack.cmp122NumericalSharedSlackLevel

physicalCoupledOneStepBoundsLevel =
  OneStep.lightweightGate4PhysicalAnalyticBoundsLevel
physicalOneStepAnalyticInputsLevel = Gate4.physicalOneStepAnalyticInputsLevel
physicalInitialUVStabilityInputsLevel = Gate4.physicalInitialUVStabilityInputsLevel
