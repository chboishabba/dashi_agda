module DASHI.Physics.YangMills.BalabanClayLiteralFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayCommonCertifiedTaylorEnclosureExact as Taylor
import DASHI.Physics.YangMills.BalabanClayT3LiteralPhysicalCoercivityProducerExact as T3
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3Remainders
import DASHI.Physics.YangMills.BalabanClayT3LiteralSU2ChartIntervalBoundsExact as T3Chart
import DASHI.Physics.YangMills.BalabanClayT3LiteralFiveRemainderConstantsExact as T3Constants
import DASHI.Physics.YangMills.BalabanClayT3LiteralCommonRadiusWitnessExact as T3Radius
import DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact as T2Activity
import DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact as T2Losses
import DASHI.Physics.YangMills.BalabanClayT2LiteralPhysicalLossWitnessExact as T2PhysicalLoss
import DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact as T2Clique
import DASHI.Physics.YangMills.BalabanClayT2PhysicalRootedPolymerEncodingExact as T2Encoding
import DASHI.Physics.YangMills.BalabanClayT2PhysicalPolymerCarrierInstanceExact as T2Carrier
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanClayT4LiteralVacuumPolarizationIntegralExact as T4Integral
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopCoefficientClosureExact as T4Closure
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5Thermo
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeTailMomentCompactnessExact as T5Quant
import DASHI.Physics.YangMills.BalabanClayBranchHeadReceiptSurface as Receipt

------------------------------------------------------------------------
-- I. Concrete finite algebra and exact reductions internalized on this branch.
------------------------------------------------------------------------

literalReferenceHodgeProducerLevel : ProofLevel
literalReferenceHodgeProducerLevel = T3.literalReferenceHodgeProducerLevel

literalPatchTransferProducerLevel : ProofLevel
literalPatchTransferProducerLevel = T3.literalPatchTransferProducerLevel

fiveTermRelativeHessianCombinationLevel : ProofLevel
fiveTermRelativeHessianCombinationLevel = T3.fiveTermRelativeHessianCombinationLevel

su2BracketFiniteAlgebraLevel : ProofLevel
su2BracketFiniteAlgebraLevel = T3Remainders.su2BracketFiniteAlgebraLevel

rightJacobianConventionSurfaceLevel : ProofLevel
rightJacobianConventionSurfaceLevel =
  T3Remainders.rightJacobianConventionSurfaceLevel

backgroundSecondVariationReductionLevel : ProofLevel
backgroundSecondVariationReductionLevel =
  T3Remainders.backgroundSecondVariationReductionLevel

fiveBackgroundRemainderCombinationLevel : ProofLevel
fiveBackgroundRemainderCombinationLevel =
  T3Remainders.fiveBackgroundRemainderCombinationLevel

hornerPolynomialReductionLevel : ProofLevel
hornerPolynomialReductionLevel = Taylor.hornerPolynomialReductionLevel

certifiedEnclosureCompositionLevel : ProofLevel
certifiedEnclosureCompositionLevel = Taylor.certifiedEnclosureCompositionLevel

literalHalfAngleSingularValueConventionLevel : ProofLevel
literalHalfAngleSingularValueConventionLevel =
  T3Chart.literalHalfAngleSingularValueConventionLevel

literalChartIntervalReductionLevel : ProofLevel
literalChartIntervalReductionLevel = T3Chart.literalChartIntervalReductionLevel

literalCurvatureConstantReductionLevel : ProofLevel
literalCurvatureConstantReductionLevel =
  T3Constants.literalCurvatureConstantReductionLevel

literalTransportChartConstantReductionLevel : ProofLevel
literalTransportChartConstantReductionLevel =
  T3Constants.literalTransportChartConstantReductionLevel

literalGaugeConstraintConstantReductionLevel : ProofLevel
literalGaugeConstraintConstantReductionLevel =
  T3Constants.literalGaugeConstraintConstantReductionLevel

literalFiveRemainderAssemblyLevel : ProofLevel
literalFiveRemainderAssemblyLevel = T3Constants.literalFiveRemainderAssemblyLevel

commonRadiusScalarCertificateReductionLevel : ProofLevel
commonRadiusScalarCertificateReductionLevel =
  T3Radius.commonRadiusScalarCertificateReductionLevel

literalFiveRemaindersBelowHalfReductionLevel : ProofLevel
literalFiveRemaindersBelowHalfReductionLevel =
  T3Radius.literalFiveRemaindersBelowHalfReductionLevel

physicalSmallFieldCoercivityFromRadiusLevel : ProofLevel
physicalSmallFieldCoercivityFromRadiusLevel =
  T3Radius.physicalSmallFieldCoercivityFromRadiusLevel

literalBadTraversalActionReductionLevel : ProofLevel
literalBadTraversalActionReductionLevel =
  T2Activity.literalBadTraversalWitnessProducerLevel

literalSixFactorCombinationLevel : ProofLevel
literalSixFactorCombinationLevel = T2Activity.literalSixFactorCombinationLevel

su2HaarDensityFormulaLevel : ProofLevel
su2HaarDensityFormulaLevel = T2Losses.su2HaarDensityFormulaLevel

relativeDeterminantReductionLevel : ProofLevel
relativeDeterminantReductionLevel = T2Losses.relativeDeterminantReductionLevel

quaternionPlaquetteBCHReductionLevel : ProofLevel
quaternionPlaquetteBCHReductionLevel =
  T2Losses.quaternionPlaquetteBCHReductionLevel

localizationPatchLossReductionLevel : ProofLevel
localizationPatchLossReductionLevel =
  T2Losses.localizationPatchLossReductionLevel

literalNetGainClosureLevel : ProofLevel
literalNetGainClosureLevel = T2Losses.literalNetGainClosureLevel

literalHaarLossAdapterLevel : ProofLevel
literalHaarLossAdapterLevel = T2PhysicalLoss.literalHaarLossAdapterLevel

literalDeterminantLossAdapterLevel : ProofLevel
literalDeterminantLossAdapterLevel =
  T2PhysicalLoss.literalDeterminantLossAdapterLevel

literalQuaternionLocalizationPatchAdapterLevel : ProofLevel
literalQuaternionLocalizationPatchAdapterLevel =
  T2PhysicalLoss.literalQuaternionLocalizationPatchAdapterLevel

literalOneSixteenthClosureAdapterLevel : ProofLevel
literalOneSixteenthClosureAdapterLevel =
  T2PhysicalLoss.literalOneSixteenthClosureAdapterLevel

literalEightWayCliqueGeometryLevel : ProofLevel
literalEightWayCliqueGeometryLevel = T2Clique.literalEightWayCliqueGeometryLevel

boundaryAwareDirectionCountLevel : ProofLevel
boundaryAwareDirectionCountLevel = T2Encoding.boundaryAwareDirectionCountLevel

literalCommonRootCliqueLevel : ProofLevel
literalCommonRootCliqueLevel = T2Encoding.literalCommonRootCliqueLevel

actualCountPartitionFunctionLevel : ProofLevel
actualCountPartitionFunctionLevel = T2Encoding.actualCountPartitionFunctionLevel

canonicalPhysicalTraceReductionLevel : ProofLevel
canonicalPhysicalTraceReductionLevel = T2Encoding.canonicalPhysicalTraceReductionLevel

canonicalRootTreeTraversalReductionLevel : ProofLevel
canonicalRootTreeTraversalReductionLevel =
  T2Carrier.canonicalRootTreeTraversalReductionLevel

physicalPatchMaskAdapterLevel : ProofLevel
physicalPatchMaskAdapterLevel = T2Carrier.physicalPatchMaskAdapterLevel

physicalCliqueAdapterLevel : ProofLevel
physicalCliqueAdapterLevel = T2Carrier.physicalCliqueAdapterLevel

localizedPlaquetteProjectionReductionLevel : ProofLevel
localizedPlaquetteProjectionReductionLevel = T4.localizedPlaquetteProjectorLevel

su2AdjointColorContractionLevel : ProofLevel
su2AdjointColorContractionLevel = T4Integral.su2AdjointColorContractionLevel

backgroundVertexDecompositionLevel : ProofLevel
backgroundVertexDecompositionLevel = T4Integral.backgroundVertexDecompositionLevel

wardTensorReductionLevel : ProofLevel
wardTensorReductionLevel = T4Integral.wardTensorReductionLevel

latticeIntegralSplitReductionLevel : ProofLevel
latticeIntegralSplitReductionLevel = T4Integral.latticeIntegralSplitReductionLevel

physicalRunningCouplingAssemblyLevel : ProofLevel
physicalRunningCouplingAssemblyLevel =
  T4Integral.physicalRunningCouplingAssemblyLevel

literalWilsonVertexReductionLevel : ProofLevel
literalWilsonVertexReductionLevel = T4Closure.literalWilsonVertexReductionLevel

literalWardKernelReductionLevel : ProofLevel
literalWardKernelReductionLevel = T4Closure.literalWardKernelReductionLevel

literalScalarIntegralReductionLevel : ProofLevel
literalScalarIntegralReductionLevel = T4Closure.literalScalarIntegralReductionLevel

literalRunningCouplingClosureLevel : ProofLevel
literalRunningCouplingClosureLevel = T4Closure.literalRunningCouplingClosureLevel

finiteGramEntrywiseToQuadraticConvergenceLevel : ProofLevel
finiteGramEntrywiseToQuadraticConvergenceLevel =
  T5.finiteGramEntrywiseToQuadraticConvergenceLevel

tailControlledCauchyReductionLevel : ProofLevel
tailControlledCauchyReductionLevel = T5Thermo.tailControlledCauchyReductionLevel

thermodynamicExpectationAssemblyLevel : ProofLevel
thermodynamicExpectationAssemblyLevel =
  T5Thermo.thermodynamicExpectationAssemblyLevel

continuumDiagonalAssemblyLevel : ProofLevel
continuumDiagonalAssemblyLevel = T5Thermo.continuumDiagonalAssemblyLevel

wilsonCylinderBoundAssemblyLevel : ProofLevel
wilsonCylinderBoundAssemblyLevel = T5Thermo.wilsonCylinderBoundAssemblyLevel

exponentialMomentToUniformIntegrabilityReductionLevel : ProofLevel
exponentialMomentToUniformIntegrabilityReductionLevel =
  T5Thermo.exponentialMomentToUniformIntegrabilityReductionLevel

physicalExpectationConvergenceAdapterLevel : ProofLevel
physicalExpectationConvergenceAdapterLevel =
  T5Thermo.physicalExpectationConvergenceAdapterLevel

boundaryClusterTailReductionLevel : ProofLevel
boundaryClusterTailReductionLevel = T5Quant.boundaryClusterTailReductionLevel

continuumDiagonalTailReductionLevel : ProofLevel
continuumDiagonalTailReductionLevel = T5Quant.continuumDiagonalTailReductionLevel

exponentialMomentUIReductionLevel : ProofLevel
exponentialMomentUIReductionLevel = T5Quant.exponentialMomentUIReductionLevel

measureCompactnessReductionLevel : ProofLevel
measureCompactnessReductionLevel = T5Quant.measureCompactnessReductionLevel

completeOSGramAdapterLevel : ProofLevel
completeOSGramAdapterLevel = T5Quant.completeOSGramAdapterLevel

------------------------------------------------------------------------
-- II. Remaining physical/real-analysis authorities.
--
-- These are deliberately finer than the old broad endpoint fields.  Supplying
-- one authority cannot silently promote a different lane.
------------------------------------------------------------------------

-- Shared scalar interval certificates.
literalTranscendentalCoefficientInputsLevel : ProofLevel
literalTranscendentalCoefficientInputsLevel =
  Taylor.literalTranscendentalCoefficientInputsLevel

literalSincTaylorCertificateInputsLevel : ProofLevel
literalSincTaylorCertificateInputsLevel =
  T3Chart.literalSincTaylorCertificateInputsLevel

-- T3: literal nonlinear Wilson/background estimates and inverse bounds.
literalFiveComponentEstimateInputsLevel : ProofLevel
literalFiveComponentEstimateInputsLevel = T3.literalFiveComponentEstimateInputsLevel

literalAdjointDexpIntervalInputsLevel : ProofLevel
literalAdjointDexpIntervalInputsLevel = conditional

literalGeometricConstantInputsLevel : ProofLevel
literalGeometricConstantInputsLevel = T3Constants.literalGeometricConstantInputsLevel

literalBackgroundCommonRadiusWitnessLevel : ProofLevel
literalBackgroundCommonRadiusWitnessLevel =
  T3Radius.literalCommonRadiusNumericalInputsLevel

physicalGreenInverseDecayInputsLevel : ProofLevel
physicalGreenInverseDecayInputsLevel = T3Radius.physicalGreenOffDiagonalInputsLevel

-- T2: the five non-action losses and common log-sixteen witness.
literalWilsonSixFactorAnalyticInputsLevel : ProofLevel
literalWilsonSixFactorAnalyticInputsLevel =
  T2Activity.literalSixComponentAnalyticInputsLevel

haarTranscendentalIntervalInputsLevel : ProofLevel
haarTranscendentalIntervalInputsLevel =
  T2Losses.haarTranscendentalIntervalInputsLevel

physicalTraceLogLocalizationInputsLevel : ProofLevel
physicalTraceLogLocalizationInputsLevel =
  T2Losses.physicalTraceLogLocalizationInputsLevel

physicalQuaternionCubicRemainderInputsLevel : ProofLevel
physicalQuaternionCubicRemainderInputsLevel =
  T2Losses.physicalQuaternionCubicRemainderInputsLevel

physicalLocalizationPatchNormInputsLevel : ProofLevel
physicalLocalizationPatchNormInputsLevel =
  T2Losses.physicalLocalizationPatchNormInputsLevel

physicalLogSixteenWitnessLevel : ProofLevel
physicalLogSixteenWitnessLevel = T2Losses.physicalLogSixteenWitnessLevel

literalPhysicalLossConstantInputsLevel : ProofLevel
literalPhysicalLossConstantInputsLevel =
  T2PhysicalLoss.literalPhysicalLossConstantInputsLevel

-- T2 geometry: actual spanning tree and patch direction masks.
physicalPolymerExtensionIdentificationLevel : ProofLevel
physicalPolymerExtensionIdentificationLevel =
  T2Clique.physicalPolymerExtensionIdentificationLevel

physicalSpanningTreeConstructionInputsLevel : ProofLevel
physicalSpanningTreeConstructionInputsLevel =
  T2Encoding.physicalSpanningTreeConstructionInputsLevel

physicalPatchDirectionMaskInputsLevel : ProofLevel
physicalPatchDirectionMaskInputsLevel =
  T2Encoding.physicalPatchDirectionMaskInputsLevel

literalPhysicalSpanningTreeInputsLevel : ProofLevel
literalPhysicalSpanningTreeInputsLevel =
  T2Carrier.literalPhysicalSpanningTreeInputsLevel

literalPhysicalDirectionMaskInputsLevel : ProofLevel
literalPhysicalDirectionMaskInputsLevel =
  T2Carrier.literalPhysicalDirectionMaskInputsLevel

-- T4: literal Wilson vertices, one-loop kernel, scalar lattice integral, and
-- quartic common-norm remainder.
literalVacuumPolarizationIntegralInputsLevel : ProofLevel
literalVacuumPolarizationIntegralInputsLevel =
  T4.literalVacuumPolarizationIntegralInputsLevel

literalWilsonVertexInputsLevel : ProofLevel
literalWilsonVertexInputsLevel = T4Integral.literalWilsonVertexInputsLevel

literalOneLoopKernelInputsLevel : ProofLevel
literalOneLoopKernelInputsLevel = T4Integral.literalOneLoopKernelInputsLevel

literalBrillouinIntegralInputsLevel : ProofLevel
literalBrillouinIntegralInputsLevel = T4Integral.literalBrillouinIntegralInputsLevel

physicalQuarticPlaquetteRemainderInputsLevel : ProofLevel
physicalQuarticPlaquetteRemainderInputsLevel =
  T4Integral.physicalQuarticPlaquetteRemainderInputsLevel

literalOneLoopDiagramInputsLevel : ProofLevel
literalOneLoopDiagramInputsLevel = T4Closure.literalOneLoopDiagramInputsLevel

literalBrillouinIntegralCertificateInputsLevel : ProofLevel
literalBrillouinIntegralCertificateInputsLevel =
  T4Closure.literalBrillouinIntegralCertificateInputsLevel

-- T5: quantitative cluster tails, diagonal cutoff control, moment bounds,
-- weak convergence and compactness.  Expectation convergence itself is now
-- assembled from these local authorities.
physicalExpectationConvergenceInputsLevel : ProofLevel
physicalExpectationConvergenceInputsLevel =
  T5.physicalExpectationConvergenceInputsLevel

physicalClusterTailInputsLevel : ProofLevel
physicalClusterTailInputsLevel = T5Thermo.physicalClusterTailInputsLevel

physicalContinuumStepTailInputsLevel : ProofLevel
physicalContinuumStepTailInputsLevel =
  T5Thermo.physicalContinuumStepTailInputsLevel

physicalExponentialMomentInputsLevel : ProofLevel
physicalExponentialMomentInputsLevel =
  T5Thermo.physicalExponentialMomentInputsLevel

physicalWeakConvergenceInputsLevel : ProofLevel
physicalWeakConvergenceInputsLevel = T5Thermo.physicalWeakConvergenceInputsLevel

physicalMeasureCompactnessInputsLevel : ProofLevel
physicalMeasureCompactnessInputsLevel =
  T5Thermo.physicalMeasureCompactnessInputsLevel

literalBoundaryClusterInputsLevel : ProofLevel
literalBoundaryClusterInputsLevel = T5Quant.literalBoundaryClusterInputsLevel

literalContinuumTailInputsLevel : ProofLevel
literalContinuumTailInputsLevel = T5Quant.literalContinuumTailInputsLevel

literalExponentialMomentInputsLevel : ProofLevel
literalExponentialMomentInputsLevel = T5Quant.literalExponentialMomentInputsLevel

literalMeasureCompactnessInputsLevel : ProofLevel
literalMeasureCompactnessInputsLevel = T5Quant.literalMeasureCompactnessInputsLevel

------------------------------------------------------------------------
-- III. User-run compiler receipt.  No Agda execution is claimed by this branch.
------------------------------------------------------------------------

cleanAgda29BranchHeadReceiptLevel : ProofLevel
cleanAgda29BranchHeadReceiptLevel = Receipt.cleanAgda29BranchHeadReceiptLevel
