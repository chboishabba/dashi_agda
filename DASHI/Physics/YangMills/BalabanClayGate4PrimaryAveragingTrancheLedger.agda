module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingTrancheLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact as Dimension
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingLocalityExact as Locality
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact as Adjoint
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkSchurBridgeExact as Schur
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkPhysicalSchurAssemblyExact as PhysicalSchur
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedMinimizerProjectionExact as Minimizer

------------------------------------------------------------------------
-- Exact primary-source and finite reductions.
------------------------------------------------------------------------

primaryAveragingNormalizationLevel =
  Dimension.primaryAveragingNormalizationLevel
dyadicDimensionArithmeticLevel = Dimension.dyadicDimensionArithmeticLevel
qkPrimaryKernelBoundProvenanceLevel =
  Dimension.qkPrimaryKernelBoundProvenanceLevel
primaryOneStepFormulaLevel = Locality.primaryOneStepFormulaLevel
localityClosedUnderCompositionLevel =
  Locality.localityClosedUnderCompositionLevel
finitePointwiseToRowSumLevel = Kernel.finitePointwiseToRowSumLevel
primaryQkLocalityToFiniteSupportLevel =
  Kernel.primaryQkLocalityToFiniteSupportLevel
primaryQkPointwiseKernelBoundLevel =
  Kernel.primaryQkPointwiseKernelBoundLevel
adjointEntryBoundFromPrimaryTransposeLevel =
  Adjoint.adjointEntryBoundFromPrimaryTransposeLevel
adjointColumnFiniteSumLevel = Adjoint.adjointColumnFiniteSumLevel
primaryQkPointwiseToStrongSchurRowsLevel =
  Schur.primaryQkPointwiseToStrongSchurRowsLevel
primaryQkStrongSchurAdapterLevel = Schur.primaryQkStrongSchurAdapterLevel
primaryQkRelativeOneEighthAssemblyLevel =
  Schur.primaryQkRelativeOneEighthAssemblyLevel
primaryQkPhysicalSchurAssemblyLevel =
  PhysicalSchur.primaryQkPhysicalSchurAssemblyLevel
primaryQkPhysicalRelativeContractionLevel =
  PhysicalSchur.primaryQkPhysicalRelativeContractionLevel
constrainedMinimizerFormulaLevel = Minimizer.constrainedMinimizerFormulaLevel
constraintProjectionKernelLevel = Minimizer.constraintProjectionKernelLevel
balabanMinimizerProvenanceLevel = Minimizer.balabanMinimizerProvenanceLevel

------------------------------------------------------------------------
-- Exact corrected boundary.
------------------------------------------------------------------------

qstarOneEighthContractionFromPrimaryCoefficientLevel =
  Dimension.qstarOneEighthContractionFromPrimaryCoefficientLevel

physicalAveragingFormulaIdentificationInputsLevel =
  Locality.physicalAveragingFormulaIdentificationInputsLevel
physicalIteratedSupportEnumerationInputsLevel =
  Locality.physicalIteratedSupportEnumerationInputsLevel
physicalQkKernelAndNormIdentificationInputsLevel =
  Kernel.physicalQkKernelAndNormIdentificationInputsLevel
physicalQkSupportCardinalityInputsLevel =
  Kernel.physicalQkSupportCardinalityInputsLevel
physicalQkAdjointTransposeIdentificationInputsLevel =
  Adjoint.physicalQkAdjointTransposeIdentificationInputsLevel
physicalQkColumnIncidenceCardinalityInputsLevel =
  Adjoint.physicalQkColumnIncidenceCardinalityInputsLevel
physicalQkAdjointTransposeMeaningInputsLevel =
  Schur.physicalQkAdjointTransposeMeaningInputsLevel
physicalQkRowColumnProductBudgetInputsLevel =
  Schur.physicalQkRowColumnProductBudgetInputsLevel
physicalQkPrimalSupportEnumerationInputsLevel =
  PhysicalSchur.physicalQkPrimalSupportEnumerationInputsLevel
physicalQkAdjointIncidenceEnumerationInputsLevel =
  PhysicalSchur.physicalQkAdjointIncidenceEnumerationInputsLevel
physicalQkNormalizedSchurBudgetInputsLevel =
  PhysicalSchur.physicalQkNormalizedSchurBudgetInputsLevel
physicalConstraintProjectionMeaningInputsLevel =
  Minimizer.physicalConstraintProjectionMeaningInputsLevel
physicalConstrainedFiniteHessianMeaningInputsLevel =
  Minimizer.physicalConstrainedFiniteHessianMeaningInputsLevel
