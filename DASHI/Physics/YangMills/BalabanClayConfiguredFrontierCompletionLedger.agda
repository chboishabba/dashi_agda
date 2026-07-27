module DASHI.Physics.YangMills.BalabanClayConfiguredFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayCommonRationalSincCertificateExact as Sinc
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredCommonRadiusCertificateExact as Radius
import DASHI.Physics.YangMills.BalabanClayT3PhysicalGreenCombesThomasExact as Green
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact as Loss
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredPhysicalPolymerCarrierExact as Polymer
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as OneLoop
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail

------------------------------------------------------------------------
-- I. Exact configured arithmetic and finite reductions.
------------------------------------------------------------------------

configuredRationalCoefficientLevel : ProofLevel
configuredRationalCoefficientLevel = Sinc.configuredRationalCoefficientLevel

configuredHornerIdentityLevel : ProofLevel
configuredHornerIdentityLevel = Sinc.configuredHornerIdentityLevel

configuredIncidenceDataLevel : ProofLevel
configuredIncidenceDataLevel = Geometry.configuredIncidenceDataLevel

configuredCoefficientArithmeticLevel : ProofLevel
configuredCoefficientArithmeticLevel = Geometry.configuredCoefficientArithmeticLevel

configuredCommonRadiusArithmeticLevel : ProofLevel
configuredCommonRadiusArithmeticLevel = Radius.configuredCommonRadiusArithmeticLevel

configuredFiveRemaindersBelowHalfLevel : ProofLevel
configuredFiveRemaindersBelowHalfLevel = Radius.configuredFiveRemaindersBelowHalfLevel

combesThomasWeightedResolventReductionLevel : ProofLevel
combesThomasWeightedResolventReductionLevel =
  Green.combesThomasWeightedResolventReductionLevel

periodicRGImageAssemblyLevel : ProofLevel
periodicRGImageAssemblyLevel = Green.periodicRGImageAssemblyLevel

configuredLossArithmeticLevel : ProofLevel
configuredLossArithmeticLevel = Loss.configuredLossArithmeticLevel

configuredOneSixteenthAssemblyLevel : ProofLevel
configuredOneSixteenthAssemblyLevel = Loss.configuredOneSixteenthAssemblyLevel

configuredPatchDirectionMaskLevel : ProofLevel
configuredPatchDirectionMaskLevel = Polymer.configuredPatchDirectionMaskLevel

configuredInteriorEightCountLevel : ProofLevel
configuredInteriorEightCountLevel = Polymer.configuredInteriorEightCountLevel

configuredCanonicalTraceAdapterLevel : ProofLevel
configuredCanonicalTraceAdapterLevel = Polymer.configuredCanonicalTraceAdapterLevel

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

------------------------------------------------------------------------
-- II. Exact remaining inhabitants after the configured reductions.
------------------------------------------------------------------------

configuredAlternatingRemainderInputsLevel : ProofLevel
configuredAlternatingRemainderInputsLevel =
  Sinc.configuredAlternatingRemainderInputsLevel

configuredNegativeLogSincInputsLevel : ProofLevel
configuredNegativeLogSincInputsLevel =
  Sinc.configuredNegativeLogSincInputsLevel

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

physicalLossDominationInputsLevel : ProofLevel
physicalLossDominationInputsLevel = Loss.physicalLossDominationInputsLevel

logSixteenIntervalReceiptLevel : ProofLevel
logSixteenIntervalReceiptLevel = Loss.logSixteenIntervalReceiptLevel

repositoryConnectedPolymerExtractionInputsLevel : ProofLevel
repositoryConnectedPolymerExtractionInputsLevel =
  Polymer.repositoryConnectedPolymerExtractionInputsLevel

literalDiagramAndBoxCertificateInputsLevel : ProofLevel
literalDiagramAndBoxCertificateInputsLevel =
  OneLoop.literalDiagramAndBoxCertificateInputsLevel

physicalClusterDiameterInputsLevel : ProofLevel
physicalClusterDiameterInputsLevel = Tail.physicalClusterDiameterInputsLevel

physicalExponentialMomentCompactnessInputsLevel : ProofLevel
physicalExponentialMomentCompactnessInputsLevel =
  Tail.physicalExponentialMomentCompactnessInputsLevel
