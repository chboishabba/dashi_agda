module DASHI.Physics.YangMills.BalabanClayFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFourAxisMartingaleExact
import DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact
import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact
import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixDimensionExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredMatrixActionExact
import DASHI.Physics.YangMills.BalabanSU2RationalAdjointRadiusExact
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact
import DASHI.Physics.YangMills.BalabanClayP1BackgroundStabilityExact
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact
import DASHI.Physics.YangMills.BalabanClayP4DyadicCoercivityBudgetExact
import DASHI.Physics.YangMills.BalabanClayP4CommonParameterDomainExact
import DASHI.Physics.YangMills.BalabanClayP5ContinuumMassGapExact

------------------------------------------------------------------------
-- Closed exact reductions.
------------------------------------------------------------------------

fourAxisMartingaleScalarAlgebraLevel : ProofLevel
fourAxisMartingaleScalarAlgebraLevel = machineChecked

scalarWilsonRieszSignAndZeroFoldLevel : ProofLevel
scalarWilsonRieszSignAndZeroFoldLevel = machineChecked

finiteMatrixProductAndInverseConsequenceLevel : ProofLevel
finiteMatrixProductAndInverseConsequenceLevel = machineChecked

physicalCoordinateEnumerationAndDeltaLevel : ProofLevel
physicalCoordinateEnumerationAndDeltaLevel = machineChecked

configuredPhysicalMatrixDimension3072Level : ProofLevel
configuredPhysicalMatrixDimension3072Level = machineChecked

configuredGaugeFixedMatrixDefinitionLevel : ProofLevel
configuredGaugeFixedMatrixDefinitionLevel = machineChecked

configuredMatrixActionLinearityLevel : ProofLevel
configuredMatrixActionLinearityLevel = machineChecked

su2RationalAdjointDisplacementAlgebraLevel : ProofLevel
su2RationalAdjointDisplacementAlgebraLevel = machineChecked

su2TraceChordalWilsonGapLevel : ProofLevel
su2TraceChordalWilsonGapLevel = machineChecked

backgroundFiveTermCombinationLevel : ProofLevel
backgroundFiveTermCombinationLevel = machineChecked

backgroundHalfMarginCoercivityLevel : ProofLevel
backgroundHalfMarginCoercivityLevel = machineChecked

finiteVolumeKPEtaHalfLevel : ProofLevel
finiteVolumeKPEtaHalfLevel = machineChecked

fiveOneStepPenaltyCombinationLevel : ProofLevel
fiveOneStepPenaltyCombinationLevel = machineChecked

oneStepCoercivityTransferAssemblyLevel : ProofLevel
oneStepCoercivityTransferAssemblyLevel = machineChecked

wardIdentityNoMassConsequenceLevel : ProofLevel
wardIdentityNoMassConsequenceLevel = machineChecked

dyadicSummableLossLevel : ProofLevel
dyadicSummableLossLevel = machineChecked

uniformOneSixtyFourthCoercivityLevel : ProofLevel
uniformOneSixtyFourthCoercivityLevel = machineChecked

commonParameterIntersectionSurfaceLevel : ProofLevel
commonParameterIntersectionSurfaceLevel = machineChecked

physicalClusteringScaleConversionLevel : ProofLevel
physicalClusteringScaleConversionLevel = machineChecked

clusteringToSpectralGapAssemblyLevel : ProofLevel
clusteringToSpectralGapAssemblyLevel = machineChecked

------------------------------------------------------------------------
-- Genuine frontier producers still to be inhabited over the literal model.
------------------------------------------------------------------------

p1NonlinearMinimizingBackgroundLevel : ProofLevel
p1NonlinearMinimizingBackgroundLevel = conditional

p1CurvatureTransportChartGaugeConstraintBoundsLevel : ProofLevel
p1CurvatureTransportChartGaugeConstraintBoundsLevel = conditional

p2GaugeInvariantBadComponentGeometryLevel : ProofLevel
p2GaugeInvariantBadComponentGeometryLevel = conditional

p2PhysicalActivityAndRootedShellEstimateLevel : ProofLevel
p2PhysicalActivityAndRootedShellEstimateLevel = conditional

p2InfiniteClusterCorrelationLevel : ProofLevel
p2InfiniteClusterCorrelationLevel = conditional

p3ExactConstrainedIntegralCoordinatesLevel : ProofLevel
p3ExactConstrainedIntegralCoordinatesLevel = conditional

p3ConstructiveSchurComplementPropagatorLevel : ProofLevel
p3ConstructiveSchurComplementPropagatorLevel = conditional

p3FivePhysicalAnalyticEstimatesLevel : ProofLevel
p3FivePhysicalAnalyticEstimatesLevel = conditional

p3WardIdentityAndRunningCouplingLevel : ProofLevel
p3WardIdentityAndRunningCouplingLevel = conditional

p4CanonicalCommonDomainInhabitationLevel : ProofLevel
p4CanonicalCommonDomainInhabitationLevel = conditional

p5FiniteMeasureAndThermodynamicLimitLevel : ProofLevel
p5FiniteMeasureAndThermodynamicLimitLevel = conditional

p5ContinuumOSAndNontrivialityLevel : ProofLevel
p5ContinuumOSAndNontrivialityLevel = conditional

p5PhysicalMassGapSurvivalLevel : ProofLevel
p5PhysicalMassGapSurvivalLevel = conditional

-- Basis expansion and literal matrix action are now concrete.  The finite
-- inverse cut has narrowed to an exact inverse-product certificate and the
-- reciprocal norm certificate for the configured 3072-coordinate matrix.
constructiveConfiguredFiniteInverseLevel : ProofLevel
constructiveConfiguredFiniteInverseLevel = conditional

-- Promote only after the complete Agda 2.9 module graph reaches the end at this
-- exact branch head.
branchHeadAuthoritativeAgda29TypecheckLevel : ProofLevel
branchHeadAuthoritativeAgda29TypecheckLevel = conditional
