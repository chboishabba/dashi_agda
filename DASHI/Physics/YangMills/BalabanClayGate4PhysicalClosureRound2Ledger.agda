module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound2Ledger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4BFAverageCoherenceScopeExact as BF
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4FiniteDimensionalFrechetChainProductExact as Frechet
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as NormPipeline
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovQuantitativeIFTReuseExact as IFTReuse
import DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovInverseStabilityExact as InverseReuse
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as HRBeta

------------------------------------------------------------------------
-- Physical closure round two.
--
-- This tranche follows the highest-alpha compression identified in the attached
-- research note.  It introduces one quantitative implicit/inverse-function
-- theorem for both the Federbush centre and the background-gauge slice; replaces
-- the remaining abstract contour-family input by an executable all-permutations
-- enumeration; derives exact Fréchet chain/product remainders; assembles the
-- physical Schur entry bound from four operator-norm stages; and reduces the
-- local H-R_beta theorem to five named local channels.
--
-- It also corrects the scope of the Torriani--Hazewinkel BF-average source and
-- keeps the current dyadic corner carrier distinct from CMP109's centred block
-- convention until the physical bridge is proved.
------------------------------------------------------------------------

bfAverageBibliographyLevel = BF.bfAverageBibliographyLevel
bfCoherenceAllDimensionsLevel = BF.bfCoherenceAllDimensionsLevel
bfFactorizedUniquenessAllDimensionsLevel =
  BF.bfFactorizedUniquenessAllDimensionsLevel
bfNonfactorizedUniquenessDimensionTwoLevel =
  BF.bfNonfactorizedUniquenessDimensionTwoLevel
bfNonfactorizedUniquenessHigherDimensionsLevel =
  BF.bfNonfactorizedUniquenessHigherDimensionsLevel
bfSourceScopeFailClosedLevel = BF.bfSourceScopeFailClosedLevel
dyadicFourDimensionalTwoStepWeightLevel =
  BF.dyadicFourDimensionalTwoStepWeightLevel
cmp109CenteredOddBlockNormalizationLevel =
  BF.cmp109CenteredOddBlockNormalizationLevel

cmp109ShortestContourEnumerationLevel =
  Contours.cmp109ShortestContourEnumerationLevel
cmp109ContourPermutationSoundnessLevel =
  Contours.cmp109ContourPermutationSoundnessLevel
cmp109ContourEndpointIndependenceLevel =
  Contours.cmp109ContourEndpointIndependenceLevel
cmp109FourActiveDirectionCount24Level =
  Contours.cmp109FourActiveDirectionCount24Level

exactFrechetChainRemainderLevel = Frechet.exactFrechetChainRemainderLevel
exactBilinearProductRemainderLevel =
  Frechet.exactBilinearProductRemainderLevel
finiteDimensionalFrechetChainRuleLevel =
  Frechet.finiteDimensionalFrechetChainRuleLevel

operatorNormThreeStagePipelineLevel =
  NormPipeline.operatorNormThreeStagePipelineLevel
operatorNormFourStagePipelineLevel =
  NormPipeline.operatorNormFourStagePipelineLevel
cmp109EntryBoundProductAssemblyLevel =
  NormPipeline.cmp109EntryBoundProductAssemblyLevel

quantitativeContractionUniquenessLevel =
  Quantitative.quantitativeContractionUniquenessLevel
quantitativeResidualSolutionUniquenessLevel =
  Quantitative.quantitativeResidualSolutionUniquenessLevel
relativeInverseKernelTrivialityLevel =
  Quantitative.relativeInverseKernelTrivialityLevel
quantitativeBanachFixedPointExistenceLevel =
  Quantitative.quantitativeBanachFixedPointExistenceLevel
finiteSquareTrivialKernelInverseUpgradeLevel =
  Quantitative.finiteSquareTrivialKernelInverseUpgradeLevel

federbushQuantitativeUniquenessAssemblyLevel =
  IFTReuse.federbushQuantitativeUniquenessAssemblyLevel
federbushImplicitDerivativeReuseLevel =
  IFTReuse.federbushImplicitDerivativeReuseLevel
backgroundSliceQuantitativeUniquenessAssemblyLevel =
  IFTReuse.backgroundSliceQuantitativeUniquenessAssemblyLevel
sharedFederbushFaddeevPopovIFTArchitectureLevel =
  IFTReuse.sharedFederbushFaddeevPopovIFTArchitectureLevel

relativeFiniteInverseKernelUpgradeLevel =
  InverseReuse.relativeFiniteInverseKernelUpgradeLevel
relativeFiniteTwoSidedInverseAssemblyLevel =
  InverseReuse.relativeFiniteTwoSidedInverseAssemblyLevel
sharedFederbushFaddeevPopovInverseArchitectureLevel =
  InverseReuse.sharedFederbushFaddeevPopovInverseArchitectureLevel

hrBetaFiveChannelLocalTriangleLevel =
  HRBeta.hrBetaFiveChannelLocalTriangleLevel
hrBetaFiveChannelLocalToUniformLevel =
  HRBeta.hrBetaFiveChannelLocalToUniformLevel
hrBetaFiveChannelPhysicalHalfAssemblyLevel =
  HRBeta.hrBetaFiveChannelPhysicalHalfAssemblyLevel

------------------------------------------------------------------------
-- Remaining physical constants and identifications.
------------------------------------------------------------------------

physicalDyadicCornerToCMP109CenteredBlockBridgeInputsLevel =
  BF.physicalDyadicCornerToCMP109CenteredBlockBridgeInputsLevel
physicalNonAbelianFederbushAverageExistenceInputsLevel =
  BF.physicalNonAbelianFederbushAverageExistenceInputsLevel

physicalPeriodicSegmentActionInputsLevel =
  Contours.physicalPeriodicSegmentActionInputsLevel
physicalCMP109BlockDisplacementIdentificationInputsLevel =
  Contours.physicalCMP109BlockDisplacementIdentificationInputsLevel

physicalCMP109ComponentRemainderLittleOInputsLevel =
  Frechet.physicalCMP109ComponentRemainderLittleOInputsLevel
physicalCMP109MatrixProductBilinearityInputsLevel =
  Frechet.physicalCMP109MatrixProductBilinearityInputsLevel

physicalOuterDexpNormInputsLevel =
  NormPipeline.physicalOuterDexpNormInputsLevel
physicalLogDexpInverseNormInputsLevel =
  NormPipeline.physicalLogDexpInverseNormInputsLevel
physicalTransportAndPathNormInputsLevel =
  NormPipeline.physicalTransportAndPathNormInputsLevel

physicalQuantitativeRadiusConstantsInputsLevel =
  Quantitative.physicalQuantitativeRadiusConstantsInputsLevel
physicalCompletenessAndBallInvarianceInputsLevel =
  Quantitative.physicalCompletenessAndBallInvarianceInputsLevel
physicalFederbushRadiusAndLipschitzInputsLevel =
  IFTReuse.physicalFederbushRadiusAndLipschitzInputsLevel
physicalFaddeevPopovRadiusAndLipschitzInputsLevel =
  IFTReuse.physicalFaddeevPopovRadiusAndLipschitzInputsLevel
physicalSharedNormConventionInputsLevel =
  IFTReuse.physicalSharedNormConventionInputsLevel
physicalFederbushCentreRelativeDefectInputsLevel =
  InverseReuse.physicalFederbushCentreRelativeDefectInputsLevel
physicalFaddeevPopovRelativeDefectInputsLevel =
  InverseReuse.physicalFaddeevPopovRelativeDefectInputsLevel
physicalFiniteSquareCarrierIdentificationInputsLevel =
  InverseReuse.physicalFiniteSquareCarrierIdentificationInputsLevel

physicalHRBetaDeterminantChannelInputsLevel =
  HRBeta.physicalHRBetaDeterminantChannelInputsLevel
physicalHRBetaInteractionChartGaugeLocalizationInputsLevel =
  HRBeta.physicalHRBetaInteractionChartGaugeLocalizationInputsLevel
physicalHRBetaPolymerLocalizationInputsLevel =
  HRBeta.physicalHRBetaPolymerLocalizationInputsLevel

physicalClosureRound2LedgerLevel : ProofLevel
physicalClosureRound2LedgerLevel = machineChecked
