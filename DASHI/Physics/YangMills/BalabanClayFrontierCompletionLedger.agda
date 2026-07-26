module DASHI.Physics.YangMills.BalabanClayFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFourAxisMartingaleExact
import DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact
import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact
import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixDimensionExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredMatrixActionExact
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact
import DASHI.Physics.YangMills.BalabanSide4TranslationConvolutionExact
import DASHI.Physics.YangMills.BalabanSide4TranslationSymmetryExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredScalarReductionExact
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact
import DASHI.Physics.YangMills.BalabanFiniteRationalCauchyExact
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenNormExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenNormExact
import DASHI.Physics.YangMills.BalabanSU2RationalAdjointRadiusExact
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact
import DASHI.Physics.YangMills.BalabanClayP1BackgroundStabilityExact
import DASHI.Physics.YangMills.BalabanClayP1PicardBackgroundConstructionExact
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact
import DASHI.Physics.YangMills.BalabanClayP3PrincipalFibreCoordinatesExact
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

fourAxisAverageGlobalMeanLevel : ProofLevel
fourAxisAverageGlobalMeanLevel = machineChecked

sideFourTranslationDifferenceLevel : ProofLevel
sideFourTranslationDifferenceLevel = machineChecked

sideFourTranslationConvolutionLevel : ProofLevel
sideFourTranslationConvolutionLevel = machineChecked

sideFourTranslationSymmetryLevel : ProofLevel
sideFourTranslationSymmetryLevel = machineChecked

sideFourScalarGreenKernelEquationLevel : ProofLevel
sideFourScalarGreenKernelEquationLevel = machineChecked

sideFourScalarGreenKernelNormalizationLevel : ProofLevel
sideFourScalarGreenKernelNormalizationLevel = machineChecked

configuredOperatorLaplacianPlusMeanReductionLevel : ProofLevel
configuredOperatorLaplacianPlusMeanReductionLevel = machineChecked

sideFourScalarGreenTwoSidedLevel : ProofLevel
sideFourScalarGreenTwoSidedLevel = machineChecked

finiteRationalCauchyLevel : ProofLevel
finiteRationalCauchyLevel = machineChecked

sideFourScalarGreenNormLevel : ProofLevel
sideFourScalarGreenNormLevel = machineChecked

configuredPhysicalGreenTwoSidedLevel : ProofLevel
configuredPhysicalGreenTwoSidedLevel = machineChecked

configuredGreenMatrixInverseProductLevel : ProofLevel
configuredGreenMatrixInverseProductLevel = machineChecked

configuredPhysicalGreenNormLevel : ProofLevel
configuredPhysicalGreenNormLevel = machineChecked

constructiveConfiguredFiniteInverseLevel : ProofLevel
constructiveConfiguredFiniteInverseLevel = machineChecked

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
-- New constructive producer-side advances.
------------------------------------------------------------------------

p1PicardBackgroundConstructionLevel : ProofLevel
p1PicardBackgroundConstructionLevel = machineChecked

p1PicardFixedPointUniquenessLevel : ProofLevel
p1PicardFixedPointUniquenessLevel = machineChecked

p2BadPathComponentConstructionLevel : ProofLevel
p2BadPathComponentConstructionLevel = machineChecked

p2BadComponentGaugeInvarianceLevel : ProofLevel
p2BadComponentGaugeInvarianceLevel = machineChecked

p3FiniteConstrainedPartitionLevel : ProofLevel
p3FiniteConstrainedPartitionLevel = machineChecked

p3FiniteEffectiveActionAdapterLevel : ProofLevel
p3FiniteEffectiveActionAdapterLevel = machineChecked

p3PrincipalFibreCoordinateConstructionLevel : ProofLevel
p3PrincipalFibreCoordinateConstructionLevel = machineChecked

p3CoordinateUniquenessDomainRepairLevel : ProofLevel
p3CoordinateUniquenessDomainRepairLevel = machineChecked

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

-- Promote only after the complete Agda 2.9 module graph reaches the end at this
-- exact branch head.
branchHeadAuthoritativeAgda29TypecheckLevel : ProofLevel
branchHeadAuthoritativeAgda29TypecheckLevel = conditional
