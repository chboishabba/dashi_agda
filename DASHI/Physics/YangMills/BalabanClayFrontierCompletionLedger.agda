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
import DASHI.Physics.YangMills.BalabanClayT1CommonAnalyticContractionExact
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact
import DASHI.Physics.YangMills.BalabanClayT2ClusterCriterionComparisonExact
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact
import DASHI.Physics.YangMills.BalabanClayP3PrincipalFibreCoordinatesExact
import DASHI.Physics.YangMills.BalabanClayT3CompactHaarLimitExact
import DASHI.Physics.YangMills.BalabanClayT3OperatorSchurComplementExact
import DASHI.Physics.YangMills.BalabanClayT3UniformFluctuationSchurExact
import DASHI.Physics.YangMills.BalabanClayT3SchurWardBetaExact
import DASHI.Physics.YangMills.BalabanClayP4DyadicCoercivityBudgetExact
import DASHI.Physics.YangMills.BalabanClayP4CommonParameterDomainExact
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact
import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact
import DASHI.Physics.YangMills.BalabanClayT4CanonicalScalarWitnessExact
import DASHI.Physics.YangMills.BalabanClayP5ContinuumMassGapExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact
import DASHI.Physics.YangMills.BalabanClayT5OSGramClosedPropertyExact

------------------------------------------------------------------------
-- Existing exact finite and reduction results.
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
-- Constructive producer-side advances.
------------------------------------------------------------------------

p1PicardBackgroundConstructionLevel : ProofLevel
p1PicardBackgroundConstructionLevel = machineChecked
p1PicardFixedPointUniquenessLevel : ProofLevel
p1PicardFixedPointUniquenessLevel = machineChecked
t1CommonAnalyticContractionLevel : ProofLevel
t1CommonAnalyticContractionLevel = machineChecked
t1CommonAnalyticSelfMapLevel : ProofLevel
t1CommonAnalyticSelfMapLevel = machineChecked
t1CommonSecondJetLevel : ProofLevel
t1CommonSecondJetLevel = machineChecked

p2BadPathComponentConstructionLevel : ProofLevel
p2BadPathComponentConstructionLevel = machineChecked
p2BadComponentGaugeInvarianceLevel : ProofLevel
p2BadComponentGaugeInvarianceLevel = machineChecked
t2WilsonActivityFactorCombinationLevel : ProofLevel
t2WilsonActivityFactorCombinationLevel = machineChecked
t2WilsonActivityOneSixteenthLevel : ProofLevel
t2WilsonActivityOneSixteenthLevel = machineChecked
t2WilsonActivityAbsoluteSignLevel : ProofLevel
t2WilsonActivityAbsoluteSignLevel = machineChecked
t2EightOverSixteenTraversalLevel : ProofLevel
t2EightOverSixteenTraversalLevel = machineChecked
t2RootedShellQuarterHalfPowerLevel : ProofLevel
t2RootedShellQuarterHalfPowerLevel = machineChecked
t2KoteckyPreissToDobrushinLevel : ProofLevel
t2KoteckyPreissToDobrushinLevel = machineChecked
t2DobrushinToFernandezProcacciLevel : ProofLevel
t2DobrushinToFernandezProcacciLevel = machineChecked
t2FernandezProcacciToExtendedGKLevel : ProofLevel
t2FernandezProcacciToExtendedGKLevel = machineChecked
t2CriterionSignConventionLevel : ProofLevel
t2CriterionSignConventionLevel = machineChecked
t2UrsellCauchyModulusLevel : ProofLevel
t2UrsellCauchyModulusLevel = machineChecked
t2ConnectedCorrelationDecayLevel : ProofLevel
t2ConnectedCorrelationDecayLevel = machineChecked

p3FiniteConstrainedPartitionLevel : ProofLevel
p3FiniteConstrainedPartitionLevel = machineChecked
p3FiniteEffectiveActionAdapterLevel : ProofLevel
p3FiniteEffectiveActionAdapterLevel = machineChecked
p3PrincipalFibreCoordinateConstructionLevel : ProofLevel
p3PrincipalFibreCoordinateConstructionLevel = machineChecked
p3CoordinateUniquenessDomainRepairLevel : ProofLevel
p3CoordinateUniquenessDomainRepairLevel = machineChecked
t3CompactHaarLimitAlgebraLevel : ProofLevel
t3CompactHaarLimitAlgebraLevel = machineChecked
t3CompactHaarWardTransportLevel : ProofLevel
t3CompactHaarWardTransportLevel = machineChecked
t3ScalarSchurNormalizationLevel : ProofLevel
t3ScalarSchurNormalizationLevel = machineChecked
t3OperatorSchurEnergyIdentityLevel : ProofLevel
t3OperatorSchurEnergyIdentityLevel = machineChecked
t3OperatorSchurP3AdapterLevel : ProofLevel
t3OperatorSchurP3AdapterLevel = machineChecked
t3UniformFluctuationCoercivityReductionLevel : ProofLevel
t3UniformFluctuationCoercivityReductionLevel = machineChecked
t3UniformFluctuationPositiveConstantLevel : ProofLevel
t3UniformFluctuationPositiveConstantLevel = machineChecked
t3GaugeReindexWardLevel : ProofLevel
t3GaugeReindexWardLevel = machineChecked
t3QuarticBetaRemainderSummabilityLevel : ProofLevel
t3QuarticBetaRemainderSummabilityLevel = machineChecked

t4BetaDerivativeFactorOfTwoLevel : ProofLevel
t4BetaDerivativeFactorOfTwoLevel = machineChecked
t4BetaZeroOverEightEqualsElevenOverTwentyFourLevel : ProofLevel
t4BetaZeroOverEightEqualsElevenOverTwentyFourLevel = machineChecked
t4RunningCouplingConventionBridgeLevel : ProofLevel
t4RunningCouplingConventionBridgeLevel = machineChecked
t4BetaNotationEquivalenceAtRecursionLevel : ProofLevel
t4BetaNotationEquivalenceAtRecursionLevel = machineChecked
p4CanonicalScalarIntersectionLevel : ProofLevel
p4CanonicalScalarIntersectionLevel = machineChecked

p5PhysicalMassInterlacingLevel : ProofLevel
p5PhysicalMassInterlacingLevel = machineChecked
p5DimensionalTransmutationNormalizationLevel : ProofLevel
p5DimensionalTransmutationNormalizationLevel = machineChecked
p5SequentialOSPropertyClosureLevel : ProofLevel
p5SequentialOSPropertyClosureLevel = machineChecked
p5OSGramQuadraticFormClosureLevel : ProofLevel
p5OSGramQuadraticFormClosureLevel = machineChecked
p5OSReflectionClosedPropertyLevel : ProofLevel
p5OSReflectionClosedPropertyLevel = machineChecked
p5FourthCumulantNontrivialityLevel : ProofLevel
p5FourthCumulantNontrivialityLevel = machineChecked

------------------------------------------------------------------------
-- Literal physical producers still to be inhabited.
------------------------------------------------------------------------

p1NonlinearMinimizingBackgroundLevel : ProofLevel
p1NonlinearMinimizingBackgroundLevel = conditional
p1CurvatureTransportChartGaugeConstraintBoundsLevel : ProofLevel
p1CurvatureTransportChartGaugeConstraintBoundsLevel = conditional
p2GaugeInvariantBadComponentGeometryLevel : ProofLevel
p2GaugeInvariantBadComponentGeometryLevel = conditional
p2PhysicalActivityAndRootedShellEstimateLevel : ProofLevel
p2PhysicalActivityAndRootedShellEstimateLevel = conditional
p2PhysicalStrictCriterionSlackLevel : ProofLevel
p2PhysicalStrictCriterionSlackLevel = conditional
p2PhysicalExtendedGKIdentificationLevel : ProofLevel
p2PhysicalExtendedGKIdentificationLevel = conditional
p2InfiniteClusterCorrelationLevel : ProofLevel
p2InfiniteClusterCorrelationLevel = conditional
p3ExactConstrainedIntegralCoordinatesLevel : ProofLevel
p3ExactConstrainedIntegralCoordinatesLevel = conditional
p3ConstructiveSchurComplementPropagatorLevel : ProofLevel
p3ConstructiveSchurComplementPropagatorLevel = conditional
p3UniformFluctuationCoercivityInputsLevel : ProofLevel
p3UniformFluctuationCoercivityInputsLevel = conditional
p3FivePhysicalAnalyticEstimatesLevel : ProofLevel
p3FivePhysicalAnalyticEstimatesLevel = conditional
p3WardIdentityAndRunningCouplingLevel : ProofLevel
p3WardIdentityAndRunningCouplingLevel = conditional
p4PhysicalPlaquetteCoefficientIdentificationLevel : ProofLevel
p4PhysicalPlaquetteCoefficientIdentificationLevel = conditional
p4CanonicalCommonDomainInhabitationLevel : ProofLevel
p4CanonicalCommonDomainInhabitationLevel = conditional
p5FiniteMeasureAndThermodynamicLimitLevel : ProofLevel
p5FiniteMeasureAndThermodynamicLimitLevel = conditional
p5PhysicalOSGramTopologyIdentificationLevel : ProofLevel
p5PhysicalOSGramTopologyIdentificationLevel = conditional
p5ContinuumOSAndNontrivialityLevel : ProofLevel
p5ContinuumOSAndNontrivialityLevel = conditional
p5PhysicalMassGapSurvivalLevel : ProofLevel
p5PhysicalMassGapSurvivalLevel = conditional
branchHeadAuthoritativeAgda29TypecheckLevel : ProofLevel
branchHeadAuthoritativeAgda29TypecheckLevel = conditional
