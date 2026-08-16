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

polymerAuditReady = Polymer.lightweightPolymerAuditReady
polymerAuditNoPromotion = Polymer.lightweightPolymerAuditNoPromotion

polymerRGHandoffLevel = Gate4.lightweightPolymerAuditRGHandoffLevel
physicalOneStepAssemblyLevel = Gate4.lightweightOneStepRGAssemblyLevel
allScaleRGAssemblyLevel = Gate4.lightweightAllScaleRGAssemblyLevel

coupledOneStepInvariantRegionLevel = OneStep.lightweightGate4OneStepRegionLevel

-- High-alpha large-field bridge:
--   pointwise R decay + rooted shell entropy
--     -> shell <= a 2^{-n}
--     -> finite large-field contribution <= 2a
--     -> shared one-step slack
--     -> invariant-region closure.
rOperationFiniteEntropyShellAssemblyLevel =
  RShell.rOperationFiniteEntropyShellAssemblyLevel
largeFieldRootedSummationLevel = LF.largeFieldRootedSummationLevel
largeFieldSharedSlackAssemblyLevel = LF.largeFieldSharedSlackAssemblyLevel
largeFieldToSharedRGErrorLevel = LFCoupled.largeFieldToSharedRGErrorLevel
largeFieldCoupledRegionClosureLevel = LFCoupled.largeFieldCoupledRegionClosureLevel

-- Fail-closed physical frontier, now split at the two actual source estimates:
-- (i) boundary-uniform pointwise R decay in the repository polymer weight;
-- (ii) rooted entropy/cardinality times that pointwise envelope fits a 2^{-n}
-- shell amplitude.  Coupling, boundary-domain, covariance/locality and initial
-- UV inputs remain separate physical estimates.
rOperationPointwiseDecayPhysicalLevel =
  RShell.rOperationPointwiseDecayPhysicalLevel
rootedPolymerEntropyTimesDecayPhysicalLevel =
  RShell.rootedPolymerEntropyTimesDecayPhysicalLevel
physicalROperationToRootedShellAmplitudeLevel =
  LF.physicalROperationToRootedShellAmplitudeLevel
physicalCoupledOneStepBoundsLevel =
  OneStep.lightweightGate4PhysicalAnalyticBoundsLevel
physicalOneStepAnalyticInputsLevel = Gate4.physicalOneStepAnalyticInputsLevel
physicalInitialUVStabilityInputsLevel = Gate4.physicalInitialUVStabilityInputsLevel
