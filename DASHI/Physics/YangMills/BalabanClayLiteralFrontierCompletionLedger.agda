module DASHI.Physics.YangMills.BalabanClayLiteralFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3LiteralPhysicalCoercivityProducerExact as T3
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3Remainders
import DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact as T2Activity
import DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact as T2Losses
import DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact as T2Clique
import DASHI.Physics.YangMills.BalabanClayT2PhysicalRootedPolymerEncodingExact as T2Encoding
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanClayT4LiteralVacuumPolarizationIntegralExact as T4Integral
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5Thermo
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

------------------------------------------------------------------------
-- II. Remaining physical/real-analysis authorities.
--
-- These are deliberately finer than the old broad endpoint fields.  Supplying
-- one authority cannot silently promote a different lane.
------------------------------------------------------------------------

-- T3: literal nonlinear Wilson/background estimates and inverse bounds.
literalFiveComponentEstimateInputsLevel : ProofLevel
literalFiveComponentEstimateInputsLevel = T3.literalFiveComponentEstimateInputsLevel

literalAdjointDexpIntervalInputsLevel : ProofLevel
literalAdjointDexpIntervalInputsLevel = conditional

literalBackgroundCommonRadiusWitnessLevel : ProofLevel
literalBackgroundCommonRadiusWitnessLevel = conditional

physicalGreenInverseDecayInputsLevel : ProofLevel
physicalGreenInverseDecayInputsLevel = conditional

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

-- T5: quantitative cluster tails, diagonal cutoff control, moment bounds,
-- weak convergence and compactness.  Expectation convergence itself is now
-- assembled from these local authorities by T5Thermo.
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

------------------------------------------------------------------------
-- III. User-run compiler receipt.  No Agda execution is claimed by this branch.
------------------------------------------------------------------------

cleanAgda29BranchHeadReceiptLevel : ProofLevel
cleanAgda29BranchHeadReceiptLevel = Receipt.cleanAgda29BranchHeadReceiptLevel
