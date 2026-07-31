module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingCurrentFrontierExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CurrentFrontierCompletionLedger as Current
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingTrancheLedger as Primary

------------------------------------------------------------------------
-- Authoritative companion to the current Gate-4 ledger.
--
-- The older current-frontier ledger remains source-compatible. This companion
-- records the primary-text corrections and the newer proof-bearing reductions
-- without silently changing the meaning of its historical Q-star fields.
------------------------------------------------------------------------

previousCurrentFrontierLevel : ProofLevel
previousCurrentFrontierLevel = Current.previousGate4LedgerLevel

primaryAveragingNormalizationLevel = Primary.primaryAveragingNormalizationLevel
averagingOperatorConventionDistinctionLevel =
  Primary.averagingOperatorConventionDistinctionLevel
primaryBibliographyMetadataLevel = Primary.primaryBibliographyMetadataLevel
cmp102AdjacentPaperSeparationLevel =
  Primary.cmp102AdjacentPaperSeparationLevel
localityClosedUnderCompositionLevel =
  Primary.localityClosedUnderCompositionLevel
finitePointwiseToRowSumLevel = Primary.finitePointwiseToRowSumLevel
adjointEntryBoundFromPrimaryTransposeLevel =
  Primary.adjointEntryBoundFromPrimaryTransposeLevel
adjointColumnFiniteSumLevel = Primary.adjointColumnFiniteSumLevel
primaryQkStrongSchurAdapterLevel = Primary.primaryQkStrongSchurAdapterLevel
primaryQkPhysicalRelativeContractionLevel =
  Primary.primaryQkPhysicalRelativeContractionLevel
finiteWeightedSchurInterfaceLevel =
  Primary.finiteWeightedSchurInterfaceLevel
primaryQkWeightedRelativeContractionLevel =
  Primary.primaryQkWeightedRelativeContractionLevel
periodicQkRowSupportEnumerationLevel =
  Primary.periodicQkRowSupportEnumerationLevel
periodicQkColumnIncidenceEnumerationLevel =
  Primary.periodicQkColumnIncidenceEnumerationLevel
periodicQkUniformRowBoundConstructionLevel =
  Primary.periodicQkUniformRowBoundConstructionLevel
periodicQkUniformColumnBoundConstructionLevel =
  Primary.periodicQkUniformColumnBoundConstructionLevel
periodicPrimaryRowBudgetInstantiationLevel =
  Primary.periodicPrimaryRowBudgetInstantiationLevel
periodicPrimaryAdjointColumnBudgetInstantiationLevel =
  Primary.periodicPrimaryAdjointColumnBudgetInstantiationLevel
constrainedMinimizerFormulaLevel = Primary.constrainedMinimizerFormulaLevel
constraintProjectionKernelLevel = Primary.constraintProjectionKernelLevel
constrainedHessianRestrictionSplitLevel =
  Primary.constrainedHessianRestrictionSplitLevel
projectedPerturbationNormTransportLevel =
  Primary.projectedPerturbationNormTransportLevel
primaryBetaFiniteDifferenceOrientationLevel =
  Primary.primaryBetaFiniteDifferenceOrientationLevel
finiteDifferenceToAdditiveRecursionLevel =
  Primary.finiteDifferenceToAdditiveRecursionLevel

-- The volume coefficient L^{-d} is not itself a relative norm theorem.
qstarOneEighthContractionFromPrimaryCoefficientLevel =
  Primary.qstarOneEighthContractionFromPrimaryCoefficientLevel

physicalAveragingConventionSelectionInputsLevel =
  Primary.physicalAveragingConventionSelectionInputsLevel
physicalAveragingFormulaIdentificationInputsLevel =
  Primary.physicalAveragingFormulaIdentificationInputsLevel
physicalQkEndpointBlockUnionPredicateInputsLevel =
  Primary.physicalQkEndpointBlockUnionPredicateInputsLevel
physicalSupportPredicateAndKernelIdentificationInputsLevel =
  Primary.physicalSupportPredicateAndKernelIdentificationInputsLevel
physicalEntryBoundCountMonotonicityInputsLevel =
  Primary.physicalEntryBoundCountMonotonicityInputsLevel
physicalQkKernelAndNormIdentificationInputsLevel =
  Primary.physicalQkKernelAndNormIdentificationInputsLevel
physicalQkAdjointTransposeIdentificationInputsLevel =
  Primary.physicalQkAdjointTransposeIdentificationInputsLevel
physicalQkNormalizedSchurBudgetInputsLevel =
  Primary.physicalQkNormalizedSchurBudgetInputsLevel
physicalPrimaryQkScaleWeightMeaningInputsLevel =
  Primary.physicalPrimaryQkScaleWeightMeaningInputsLevel
physicalPrimaryQkWeightedProductBudgetInputsLevel =
  Primary.physicalPrimaryQkWeightedProductBudgetInputsLevel
physicalConstraintProjectionMeaningInputsLevel =
  Primary.physicalConstraintProjectionMeaningInputsLevel
physicalConstrainedFiniteHessianMeaningInputsLevel =
  Primary.physicalConstrainedFiniteHessianMeaningInputsLevel
physicalHessianSecondVariationSplitInputsLevel =
  Primary.physicalHessianSecondVariationSplitInputsLevel
physicalAmbientHessianPerturbationBoundInputsLevel =
  Primary.physicalAmbientHessianPerturbationBoundInputsLevel
physicalPrimaryBetaFunctionIdentificationInputsLevel =
  Primary.physicalPrimaryBetaFunctionIdentificationInputsLevel
physicalPrimaryAdmissibleIntervalInputsLevel =
  Primary.physicalPrimaryAdmissibleIntervalInputsLevel
physicalHRBetaRemainderUniformityInputsLevel =
  Primary.physicalHRBetaRemainderUniformityInputsLevel

primaryAveragingCurrentFrontierCompanionLevel : ProofLevel
primaryAveragingCurrentFrontierCompanionLevel = machineChecked
