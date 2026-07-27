module DASHI.Physics.YangMills.BalabanClayConfiguredFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayCommonRationalSincCertificateExact as Sinc
import DASHI.Physics.YangMills.BalabanClayCommonLogSixteenCertificateExact as Log16
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredCommonRadiusCertificateExact as Radius
import DASHI.Physics.YangMills.BalabanClayT3PhysicalGreenCombesThomasExact as Green
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact as Loss
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredPhysicalPolymerCarrierExact as Polymer
import DASHI.Physics.YangMills.BalabanClayT4Balaban536VacuumPolarizationTargetExact as Balaban536
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as OneLoop
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT5RootedShellBoundaryTailExact as ShellTail

------------------------------------------------------------------------
-- I. Exact configured arithmetic and finite reductions.
------------------------------------------------------------------------

configuredRationalCoefficientLevel : ProofLevel
configuredRationalCoefficientLevel = Sinc.configuredRationalCoefficientLevel

configuredHornerIdentityLevel : ProofLevel
configuredHornerIdentityLevel = Sinc.configuredHornerIdentityLevel

logSixteenFinitePartialSumArithmeticLevel : ProofLevel
logSixteenFinitePartialSumArithmeticLevel =
  Log16.logSixteenFinitePartialSumArithmeticLevel

logSixteenMonotoneReductionLevel : ProofLevel
logSixteenMonotoneReductionLevel = Log16.logSixteenMonotoneReductionLevel

configuredIncidenceDataLevel : ProofLevel
configuredIncidenceDataLevel = Geometry.configuredIncidenceDataLevel

configuredCoefficientArithmeticLevel : ProofLevel
configuredCoefficientArithmeticLevel = Geometry.configuredCoefficientArithmeticLevel

configuredCommonRadiusArithmeticLevel : ProofLevel
configuredCommonRadiusArithmeticLevel = Radius.configuredCommonRadiusArithmeticLevel

configuredFiveRemaindersBelowHalfLevel : ProofLevel
configuredFiveRemaindersBelowHalfLevel = Radius.configuredFiveRemaindersBelowHalfLevel

localCombesThomasReductionLevel : ProofLevel
localCombesThomasReductionLevel = Green.localCombesThomasReductionLevel

fourierRGImageAssemblyLevel : ProofLevel
fourierRGImageAssemblyLevel = Green.fourierRGImageAssemblyLevel

configuredLossArithmeticLevel : ProofLevel
configuredLossArithmeticLevel = Loss.configuredLossArithmeticLevel

configuredLogSixteenReductionLevel : ProofLevel
configuredLogSixteenReductionLevel = Loss.configuredLogSixteenReductionLevel

configuredOneSixteenthAssemblyLevel : ProofLevel
configuredOneSixteenthAssemblyLevel = Loss.configuredOneSixteenthAssemblyLevel

configuredPatchDirectionMaskLevel : ProofLevel
configuredPatchDirectionMaskLevel = Polymer.configuredPatchDirectionMaskLevel

configuredInteriorEightCountLevel : ProofLevel
configuredInteriorEightCountLevel = Polymer.configuredInteriorEightCountLevel

configuredCanonicalTraceAdapterLevel : ProofLevel
configuredCanonicalTraceAdapterLevel = Polymer.configuredCanonicalTraceAdapterLevel

balaban536LaurentReductionLevel : ProofLevel
balaban536LaurentReductionLevel = Balaban536.balaban536LaurentReductionLevel

balaban537MomentumReductionLevel : ProofLevel
balaban537MomentumReductionLevel = Balaban536.balaban537MomentumReductionLevel

balaban541CoefficientExtractionLevel : ProofLevel
balaban541CoefficientExtractionLevel =
  Balaban536.balaban541CoefficientExtractionLevel

universalColorCoefficientArithmeticLevel : ProofLevel
universalColorCoefficientArithmeticLevel =
  OneLoop.universalColorCoefficientArithmeticLevel

brillouinBoxSummationReductionLevel : ProofLevel
brillouinBoxSummationReductionLevel =
  OneLoop.brillouinBoxSummationReductionLevel

configuredPlaquetteCoefficientAssemblyLevel : ProofLevel
configuredPlaquetteCoefficientAssemblyLevel =
  OneLoop.configuredPlaquetteCoefficientAssemblyLevel

configuredDyadicTailArithmeticLevel : ProofLevel
configuredDyadicTailArithmeticLevel = Tail.configuredDyadicTailArithmeticLevel

configuredBoundaryTailReductionLevel : ProofLevel
configuredBoundaryTailReductionLevel = Tail.configuredBoundaryTailReductionLevel

configuredContinuumTailReductionLevel : ProofLevel
configuredContinuumTailReductionLevel = Tail.configuredContinuumTailReductionLevel

rootedShellToBoundaryTailReductionLevel : ProofLevel
rootedShellToBoundaryTailReductionLevel =
  ShellTail.rootedShellToBoundaryTailReductionLevel

------------------------------------------------------------------------
-- II. Exact remaining inhabitants after the configured reductions.
------------------------------------------------------------------------

configuredAlternatingRemainderInputsLevel : ProofLevel
configuredAlternatingRemainderInputsLevel =
  Sinc.configuredAlternatingRemainderInputsLevel

configuredNegativeLogSincInputsLevel : ProofLevel
configuredNegativeLogSincInputsLevel =
  Sinc.configuredNegativeLogSincInputsLevel

exponentialPositiveTailInputsLevel : ProofLevel
exponentialPositiveTailInputsLevel = Log16.exponentialPositiveTailInputsLevel

literalConfiguredRemainderDominationInputsLevel : ProofLevel
literalConfiguredRemainderDominationInputsLevel =
  Geometry.literalConfiguredRemainderDominationInputsLevel

configuredPhysicalRemainderEstimateInputsLevel : ProofLevel
configuredPhysicalRemainderEstimateInputsLevel =
  Radius.configuredPhysicalRemainderEstimateInputsLevel

physicalFiniteRangeGapInputsLevel : ProofLevel
physicalFiniteRangeGapInputsLevel = Green.physicalFiniteRangeGapInputsLevel

physicalFourierRGImageInputsLevel : ProofLevel
physicalFourierRGImageInputsLevel = Green.physicalFourierRGImageInputsLevel

periodicRandomWalkTransferInputsLevel : ProofLevel
periodicRandomWalkTransferInputsLevel = Green.periodicRandomWalkTransferInputsLevel

physicalLossDominationInputsLevel : ProofLevel
physicalLossDominationInputsLevel = Loss.physicalLossDominationInputsLevel

repositoryConnectedPolymerExtractionInputsLevel : ProofLevel
repositoryConnectedPolymerExtractionInputsLevel =
  Polymer.repositoryConnectedPolymerExtractionInputsLevel

literalDiagramToBalabanTargetInputsLevel : ProofLevel
literalDiagramToBalabanTargetInputsLevel =
  Balaban536.literalDiagramToBalabanTargetInputsLevel

literalDiagramAndBoxCertificateInputsLevel : ProofLevel
literalDiagramAndBoxCertificateInputsLevel =
  OneLoop.literalDiagramAndBoxCertificateInputsLevel

physicalClusterDiameterInputsLevel : ProofLevel
physicalClusterDiameterInputsLevel = Tail.physicalClusterDiameterInputsLevel

boundaryEscapeInputsLevel : ProofLevel
boundaryEscapeInputsLevel = ShellTail.boundaryEscapeInputsLevel

physicalExponentialMomentCompactnessInputsLevel : ProofLevel
physicalExponentialMomentCompactnessInputsLevel =
  Tail.physicalExponentialMomentCompactnessInputsLevel
