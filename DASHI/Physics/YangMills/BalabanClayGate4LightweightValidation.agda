module DASHI.Physics.YangMills.BalabanClayGate4LightweightValidation where

------------------------------------------------------------------------
-- Lightweight Gate-4 validation root.
--
-- This intentionally imports only the P06/P07/P08/P09 theorem-surface audit,
-- the exact physical RG handoff, the rational common-budget theorem, and the
-- new rooted large-field -> shared-slack bridge.  It does not import
-- BalabanPolymerDiameterEntropy, SFGC, or the triadic Closure graph which
-- caused the host-memory failure.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropyLight as Polymer
import DASHI.Physics.YangMills.BalabanClayGate4LightweightPolymerRGHandoffExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4LightweightOneStepRegionExact as OneStep
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF
import DASHI.Physics.YangMills.BalabanYM4LargeFieldCoupledStepExact as LFCoupled

polymerAuditReady = Polymer.lightweightPolymerAuditReady
polymerAuditNoPromotion = Polymer.lightweightPolymerAuditNoPromotion

polymerRGHandoffLevel = Gate4.lightweightPolymerAuditRGHandoffLevel
physicalOneStepAssemblyLevel = Gate4.lightweightOneStepRGAssemblyLevel
allScaleRGAssemblyLevel = Gate4.lightweightAllScaleRGAssemblyLevel

coupledOneStepInvariantRegionLevel = OneStep.lightweightGate4OneStepRegionLevel

-- New high-alpha bridge: a rooted shell bound a*2^{-n} gives finite large-field
-- contribution <= 2a, and the shared slack inequality feeds that contribution
-- into the exact common one-step invariant-region theorem.
largeFieldRootedSummationLevel = LF.largeFieldRootedSummationLevel
largeFieldSharedSlackAssemblyLevel = LF.largeFieldSharedSlackAssemblyLevel
largeFieldToSharedRGErrorLevel = LFCoupled.largeFieldToSharedRGErrorLevel
largeFieldCoupledRegionClosureLevel = LFCoupled.largeFieldCoupledRegionClosureLevel

-- Fail-closed analytic frontier.  The remaining large-field producer is now
-- precisely the physical identification of Bałaban's boundary-uniform
-- R-operation activity with the rooted shell amplitude in the SAME polymer
-- norm.  Coupling, boundary-domain, covariance/locality and initial UV inputs
-- remain separate physical estimates.
physicalROperationToRootedShellAmplitudeLevel =
  LF.physicalROperationToRootedShellAmplitudeLevel
physicalCoupledOneStepBoundsLevel =
  OneStep.lightweightGate4PhysicalAnalyticBoundsLevel
physicalOneStepAnalyticInputsLevel = Gate4.physicalOneStepAnalyticInputsLevel
physicalInitialUVStabilityInputsLevel = Gate4.physicalInitialUVStabilityInputsLevel
