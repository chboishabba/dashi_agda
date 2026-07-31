module DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkWeightedSchurExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact as Adjoint
import DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurBlockAdjointExact as Weighted

------------------------------------------------------------------------
-- Primary Q_k attachment to the weighted Schur theorem.
--
-- The weighted theorem is useful only if its kernel is the derivative of the
-- selected physical Bałaban averaging convention.  This record makes that
-- identification explicit and retains the finite adjoint-transpose package.
-- It deliberately does not infer a particular scale weight from the CMP 98 or
-- CMP 109 averaging coefficient.
------------------------------------------------------------------------

record PrimaryQkWeightedSchurMeaning
    (Input Output Scalar : Set) : Set₁ where
  field
    additive : Primary.OrderedAdditiveScale Scalar

    primaryRows : Primary.UniformFiniteKernelBudget
      Output Input Scalar additive

    primaryAdjointColumns : Adjoint.UniformPrimaryQkAdjointColumnBudget
      Output Input Scalar additive

    primalAgreement :
      Primary.rowData primaryRows
      ≡ Adjoint.primalRows
          (Adjoint.adjointMeaning primaryAdjointColumns)

    weightedData : Weighted.FiniteWeightedSchurData
      Input Output Scalar

    weightedKernelIsPrimaryDerivative :
      Weighted.Kernel weightedData
      ≡ Primary.kernelAbsoluteValue
          (Primary.rowData primaryRows)

    WeightedAdjointMeaning :
      (Input → Output → Scalar) → Set

    weightedAdjointMeaning :
      WeightedAdjointMeaning
        (Adjoint.adjointKernelAbsoluteValue
          (Adjoint.adjointMeaning primaryAdjointColumns))

    relativeBudget : Weighted.RelativeWeightedSchurBudget weightedData

open PrimaryQkWeightedSchurMeaning public

primaryQkWeightedRelativeOneEighth :
  ∀ {Input Output Scalar : Set}
    (meaning : PrimaryQkWeightedSchurMeaning Input Output Scalar) →
  Weighted.LessEqual (weightedData meaning)
    (Weighted.operatorNormSquared (weightedData meaning))
    (Weighted.multiply (weightedData meaning)
      (Weighted.oneEighth (relativeBudget meaning))
      (Weighted.previousNormSquared (relativeBudget meaning)))
primaryQkWeightedRelativeOneEighth meaning =
  Weighted.finiteWeightedSchurImpliesRelativeOneEighth
    (relativeBudget meaning)

primaryQkWeightedKernelAttachmentLevel : ProofLevel
primaryQkWeightedKernelAttachmentLevel = machineChecked

primaryQkWeightedRelativeContractionLevel : ProofLevel
primaryQkWeightedRelativeContractionLevel = machineChecked

physicalPrimaryQkWeightedSumInputsLevel : ProofLevel
physicalPrimaryQkWeightedSumInputsLevel = conditional

physicalPrimaryQkScaleWeightMeaningInputsLevel : ProofLevel
physicalPrimaryQkScaleWeightMeaningInputsLevel = conditional

physicalPrimaryQkWeightedProductBudgetInputsLevel : ProofLevel
physicalPrimaryQkWeightedProductBudgetInputsLevel = conditional
