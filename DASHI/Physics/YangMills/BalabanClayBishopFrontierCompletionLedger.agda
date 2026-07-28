module DASHI.Physics.YangMills.BalabanClayBishopFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as BishopSeries
import DASHI.Foundations.RealElementaryFunctionsBishopTransportExact as BishopTransport
import DASHI.Foundations.RealElementaryFunctionsCanonicalInstanceExact as CanonicalReal

import DASHI.Physics.YangMills.BalabanClayT3LiteralFixedAtomFormulaInstanceExact as AtomFormula
import DASHI.Physics.YangMills.BalabanClayT3PeriodicHessianKernelFormulaExact as HessianFormula

import DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact as QuaternionNormalization
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as PeriodicBFS

import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact as OneLoopConvention
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as OneLoopEvaluator

import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as MarkedFP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalRootedShellInjectionExact as ShellInjection
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as PhysicalT5

------------------------------------------------------------------------
-- I. Newly internalized constructive and finite data.
------------------------------------------------------------------------

bishopConcreteRealCarrierLevel = Bishop.bishopConcreteRealCarrierLevel
bishopCauchyCompletenessLevel = Bishop.bishopCauchyCompletenessLevel
bishopAbsoluteSeriesTransferLevel = Bishop.bishopAbsoluteSeriesTransferLevel
bishopPowerSeriesDefinitionsLevel = BishopSeries.bishopPowerSeriesDefinitionsLevel
bishopPowerSeriesCompletenessLevel = BishopSeries.bishopPowerSeriesCompletenessLevel
bishopBackedFunctionDefinitionsLevel =
  BishopTransport.bishopBackedFunctionDefinitionsLevel
bishopConcreteCompletenessImportedLevel =
  CanonicalReal.bishopConcreteCompletenessImportedLevel
bishopPowerSeriesLimitConstructionLevel =
  CanonicalReal.bishopPowerSeriesLimitConstructionLevel

literalFixedAtomFormulaLevel = AtomFormula.literalFixedAtomFormulaLevel
literalFixedAtomEnumerationLevel = AtomFormula.literalFixedAtomEnumerationLevel

literalPeriodicKernelAlgebraLevel =
  HessianFormula.literalPeriodicKernelAlgebraLevel
literalWeightedConjugationFormulaLevel =
  HessianFormula.literalWeightedConjugationFormulaLevel
literalFourierSymbolFormulaLevel =
  HessianFormula.literalFourierSymbolFormulaLevel
literalRGGreenDifferenceLevel =
  HessianFormula.literalRGGreenDifferenceLevel

bishopQuaternionAlgebraLevel =
  QuaternionNormalization.bishopQuaternionAlgebraLevel
bishopQuaternionJetFormulaLevel =
  QuaternionNormalization.bishopQuaternionJetFormulaLevel

periodicSuccessorPredecessorDefinitionLevel =
  PeriodicBFS.periodicSuccessorPredecessorDefinitionLevel
periodicSignedStepDefinitionLevel =
  PeriodicBFS.periodicSignedStepDefinitionLevel
periodicAdjacencyDecisionLevel =
  PeriodicBFS.periodicAdjacencyDecisionLevel
periodicConnectedPolymerCarrierLevel =
  PeriodicBFS.periodicConnectedPolymerCarrierLevel

canonicalOneLoopConventionLevel =
  OneLoopConvention.canonicalConventionLevel
universalCoefficientNormalizationLevel =
  OneLoopConvention.universalCoefficientNormalizationLevel
literalDiagramExpressionLevel =
  OneLoopEvaluator.literalDiagramExpressionLevel
recursiveIntervalEvaluationLevel =
  OneLoopEvaluator.recursiveIntervalEvaluationLevel
literalGeneratedGridAdapterLevel =
  OneLoopEvaluator.literalGeneratedGridAdapterLevel

kpCriterionSeparatedLevel = MarkedFP.kpCriterionSeparatedLevel
fpEightCliqueArithmeticLevel = MarkedFP.fpEightCliqueArithmeticLevel
markedFPSlackArithmeticLevel = MarkedFP.markedFPSlackArithmeticLevel
rootedShellDecoderInjectivityLevel =
  ShellInjection.rootedShellDecoderInjectivityLevel
boundaryDistanceReductionLevel = ShellInjection.boundaryDistanceReductionLevel
finiteDyadicTelescopingLevel = PhysicalT5.finiteDyadicTelescopingLevel
physicalClusterExpansionAdapterLevel =
  PhysicalT5.physicalClusterExpansionAdapterLevel
physicalMarkedMomentAdapterLevel = PhysicalT5.physicalMarkedMomentAdapterLevel

------------------------------------------------------------------------
-- II. Remaining irreducible analytic/model-specific inhabitants.
--
-- These are not promoted by the presence of the Bishop submodule or generated
-- finite carriers.  Each conditional status names a concrete local theorem.
------------------------------------------------------------------------

bishopToDASHITransportInputsLevel = Bishop.bishopToDASHITransportInputsLevel
bishopElementaryCoefficientTailInputsLevel =
  BishopSeries.bishopElementaryCoefficientTailInputsLevel
bishopToLegacyRealTransportLevel =
  BishopTransport.bishopToLegacyRealTransportLevel
legacyElementaryAuthorityAgreementLevel =
  BishopTransport.legacyElementaryAuthorityAgreementLevel

literalFixedAtomInequalityInputsLevel =
  AtomFormula.literalFixedAtomInequalityInputsLevel
literalHoppingStripAndImageInputsLevel =
  HessianFormula.literalHoppingStripAndImageInputsLevel

bishopQuaternionTranscendentalTailInputsLevel =
  QuaternionNormalization.bishopQuaternionTranscendentalTailInputsLevel
quaternionCollarCountingInputsLevel =
  QuaternionNormalization.quaternionCollarCountingInputsLevel

periodicBFSShortestPathProofInputsLevel =
  PeriodicBFS.periodicBFSShortestPathProofInputsLevel
periodicDFSDecoderProofInputsLevel =
  PeriodicBFS.periodicDFSDecoderProofInputsLevel

literalDiagramWardAndBoxReceiptInputsLevel =
  OneLoopEvaluator.literalDiagramWardAndBoxReceiptInputsLevel

markedFPClusterInputsLevel = MarkedFP.markedFPClusterInputsLevel
physicalBoundaryCrossingGeometryInputsLevel =
  ShellInjection.physicalBoundaryCrossingGeometryInputsLevel
physicalRootedShellWeightInputsLevel =
  ShellInjection.physicalRootedShellWeightInputsLevel
physicalClusterCancellationInputsLevel =
  PhysicalT5.physicalClusterCancellationInputsLevel
physicalRGDefectInputsLevel = PhysicalT5.physicalRGDefectInputsLevel
physicalMomentCompactnessInputsLevel =
  PhysicalT5.physicalMomentCompactnessInputsLevel
