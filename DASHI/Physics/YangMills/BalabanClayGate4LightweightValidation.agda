module DASHI.Physics.YangMills.BalabanClayGate4LightweightValidation where

------------------------------------------------------------------------
-- Lightweight Gate-4 validation root.
--
-- This intentionally imports only the P06/P07/P08/P09 theorem-surface audit,
-- exact physical RG handoff, source-sized R-operation lane, and source
-- covariance/boundary/coupling authorities.  It does not import the heavyweight
-- BalabanPolymerDiameterEntropy, SFGC, or triadic Closure graph.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropyLight as Polymer
import DASHI.Physics.YangMills.BalabanClayGate4LightweightPolymerRGHandoffExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4LightweightOneStepRegionExact as OneStep
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as RShell
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF
import DASHI.Physics.YangMills.BalabanYM4LargeFieldCoupledStepExact as LFCoupled
import DASHI.Physics.YangMills.BalabanCMP109LocalizationTreeSizeDictionaryExact as TreeSize
import DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact as Eq1100
import DASHI.Physics.YangMills.BalabanCMP122Equation1100EntropyBudgetExact as EqEntropy
import DASHI.Physics.YangMills.BalabanCMP122Equation1100SharedSlackExact as EqSlack
import DASHI.Physics.YangMills.BalabanCMP119RDecayReserveBudgetExact as Reserve
import DASHI.Physics.YangMills.BalabanCMP119CMP122BoundaryReinjectionSourceExact as Boundary
import DASHI.Physics.YangMills.BalabanCMP99CovarianceLocalityToRGStateExact as Covariance
import DASHI.Physics.YangMills.Balaban1989SmallCouplingToRGCapExact as Coupling

polymerAuditReady = Polymer.lightweightPolymerAuditReady
polymerAuditNoPromotion = Polymer.lightweightPolymerAuditNoPromotion

polymerRGHandoffLevel = Gate4.lightweightPolymerAuditRGHandoffLevel
physicalOneStepAssemblyLevel = Gate4.lightweightOneStepRGAssemblyLevel
allScaleRGAssemblyLevel = Gate4.lightweightAllScaleRGAssemblyLevel
coupledOneStepInvariantRegionLevel = OneStep.lightweightGate4OneStepRegionLevel

-- Source-sized large-field bridge.
cmp109LocalizationDomainTreeDefinitionLevel =
  TreeSize.cmp109LocalizationDomainTreeDefinitionLevel
cmp109ExactTreeMetricTransportLevel = TreeSize.cmp109ExactTreeMetricTransportLevel
cmp109DominatingTreeMetricTransportLevel =
  TreeSize.cmp109DominatingTreeMetricTransportLevel
cmp122Equation1100PrimarySourceLevel = Eq1100.cmp122Equation1100PrimarySourceLevel
cmp119Equation231ArbitraryDecayReserveLevel =
  Eq1100.cmp119Equation231ArbitraryDecayReserveLevel
cmp119ThreeWayDecayReserveArithmeticLevel =
  Reserve.cmp119ThreeWayDecayReserveArithmeticLevel
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

-- Published boundary/covariance authorities and exact small-coupling cap
-- transport.  The latter uses only Bałaban's explicit small-coupling hypothesis
-- and does not pretend to prove the deferred positive-beta calculation.
cmp119BoundaryAnalyticityAndDecayLevel =
  Boundary.cmp119BoundaryAnalyticityAndDecayLevel
cmp122BoundaryReinjectionPreservationLevel =
  Boundary.cmp122BoundaryReinjectionPreservationLevel
cmp99BackgroundPropagatorDecayAuthorityLevel =
  Covariance.cmp99BackgroundPropagatorDecayAuthorityLevel
cmp99NextStateCovarianceTransportLevel =
  Covariance.cmp99NextStateCovarianceTransportLevel
balabanSmallCouplingHypothesisAuthorityLevel =
  Coupling.balabanSmallCouplingHypothesisAuthorityLevel
balabanSmallCouplingToRGCapTransportLevel =
  Coupling.balabanSmallCouplingToRGCapTransportLevel

-- Fail-closed physical frontier.  The primary papers now own the abstract
-- decay/locality and small-coupling conditional theorems; these are the
-- representation, history and numerical leaves which must be instantiated on
-- the literal repository state.
cmp109RepositoryLocalizationDomainIdentificationLevel =
  TreeSize.cmp109RepositoryLocalizationDomainIdentificationLevel
cmp119SourceDistanceToRepositoryDiameterLevel =
  Reserve.cmp119SourceDistanceToRepositoryDiameterLevel
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
cmp119CMP122BoundaryRepositoryDictionaryLevel =
  Boundary.cmp119CMP122BoundaryRepositoryDictionaryLevel
cmp99NextBackgroundRegularityLevel = Covariance.cmp99NextBackgroundRegularityLevel
cmp99RepositoryCovarianceDictionaryLevel =
  Covariance.cmp99RepositoryCovarianceDictionaryLevel
balabanPhysicalSmallCouplingHistoryLevel =
  Coupling.balabanPhysicalSmallCouplingHistoryLevel

physicalCoupledOneStepBoundsLevel =
  OneStep.lightweightGate4PhysicalAnalyticBoundsLevel
physicalOneStepAnalyticInputsLevel = Gate4.physicalOneStepAnalyticInputsLevel
physicalInitialUVStabilityInputsLevel = Gate4.physicalInitialUVStabilityInputsLevel
