module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingCurrentFrontierExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CurrentFrontierCompletionLedger as Current
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingTrancheLedger as Primary

------------------------------------------------------------------------
-- Authoritative companion to the current Gate-4 ledger.
--
-- The older current-frontier ledger remains source-compatible. This companion
-- records the primary-text correction and the new proof-bearing reductions
-- without silently changing the meaning of its historical Q-star fields.
------------------------------------------------------------------------

previousCurrentFrontierLevel : ProofLevel
previousCurrentFrontierLevel = Current.previousGate4LedgerLevel

primaryAveragingNormalizationLevel = Primary.primaryAveragingNormalizationLevel
localityClosedUnderCompositionLevel =
  Primary.localityClosedUnderCompositionLevel
finitePointwiseToRowSumLevel = Primary.finitePointwiseToRowSumLevel
adjointEntryBoundFromPrimaryTransposeLevel =
  Primary.adjointEntryBoundFromPrimaryTransposeLevel
adjointColumnFiniteSumLevel = Primary.adjointColumnFiniteSumLevel
primaryQkStrongSchurAdapterLevel = Primary.primaryQkStrongSchurAdapterLevel
primaryQkPhysicalRelativeContractionLevel =
  Primary.primaryQkPhysicalRelativeContractionLevel
constrainedMinimizerFormulaLevel = Primary.constrainedMinimizerFormulaLevel
constraintProjectionKernelLevel = Primary.constraintProjectionKernelLevel

-- The volume coefficient L^{-d} is not itself a relative norm theorem.
qstarOneEighthContractionFromPrimaryCoefficientLevel =
  Primary.qstarOneEighthContractionFromPrimaryCoefficientLevel

physicalAveragingFormulaIdentificationInputsLevel =
  Primary.physicalAveragingFormulaIdentificationInputsLevel
physicalIteratedSupportEnumerationInputsLevel =
  Primary.physicalIteratedSupportEnumerationInputsLevel
physicalQkKernelAndNormIdentificationInputsLevel =
  Primary.physicalQkKernelAndNormIdentificationInputsLevel
physicalQkSupportCardinalityInputsLevel =
  Primary.physicalQkSupportCardinalityInputsLevel
physicalQkAdjointTransposeIdentificationInputsLevel =
  Primary.physicalQkAdjointTransposeIdentificationInputsLevel
physicalQkColumnIncidenceCardinalityInputsLevel =
  Primary.physicalQkColumnIncidenceCardinalityInputsLevel
physicalQkNormalizedSchurBudgetInputsLevel =
  Primary.physicalQkNormalizedSchurBudgetInputsLevel
physicalConstraintProjectionMeaningInputsLevel =
  Primary.physicalConstraintProjectionMeaningInputsLevel
physicalConstrainedFiniteHessianMeaningInputsLevel =
  Primary.physicalConstrainedFiniteHessianMeaningInputsLevel

primaryAveragingCurrentFrontierCompanionLevel : ProofLevel
primaryAveragingCurrentFrontierCompanionLevel = machineChecked
