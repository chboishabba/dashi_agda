module DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkPhysicalSchurAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact as Adjoint
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkSchurBridgeExact as Bridge

------------------------------------------------------------------------
-- One physical package for the primary Q_k route.
--
-- Balaban supplies locality and the pointwise derivative-kernel bound. DASHI
-- must still instantiate the finite support lists, their row and column incidence
-- budgets, the adjoint transpose meaning, and the normalized Schur inequality.
-- Once those are present, there is no further analytic step between the primary
-- kernel theorem and the selected relative squared-norm bound.
------------------------------------------------------------------------

record PhysicalPrimaryQkSchurAssembly
    (Input Output Scalar : Set) : Set₁ where
  field
    additive : Primary.OrderedAdditiveScale Scalar
    multiply : Scalar → Scalar → Scalar

    primalRows : Primary.UniformFiniteKernelBudget
      Output Input Scalar additive
    adjointColumns : Adjoint.UniformPrimaryQkAdjointColumnBudget
      Output Input Scalar additive

    primalAgreement :
      Primary.rowData primalRows
      ≡ Adjoint.primalRows (Adjoint.adjointMeaning adjointColumns)

    operatorNormSquared : Scalar
    finiteSchurTest :
      Primary.LessEqual additive operatorNormSquared
        (multiply
          (Primary.uniformBudget primalRows)
          (Adjoint.uniformColumnBudget adjointColumns))

open PhysicalPrimaryQkSchurAssembly public

asStrongPrimaryQkSchurData :
  ∀ {Input Output Scalar : Set} →
  PhysicalPrimaryQkSchurAssembly Input Output Scalar →
  Bridge.StrongPrimaryQkSchurData Input Output Scalar
asStrongPrimaryQkSchurData dataSet = record
  { additive = additive dataSet
  ; multiply = multiply dataSet
  ; rowKernel = primalRows dataSet
  ; columnKernel =
      Adjoint.asUniformAdjointColumnKernelBudget (adjointColumns dataSet)
  ; columnIsAdjointTranspose = λ input output →
      trans
        (Adjoint.adjointTransposeExact
          (Adjoint.adjointMeaning (adjointColumns dataSet)) input output)
        (cong
          (λ rows → Primary.kernelAbsoluteValue rows output input)
          (sym (primalAgreement dataSet)))
  ; operatorNormSquared = operatorNormSquared dataSet
  ; finiteSchurTest = finiteSchurTest dataSet
  }

record PhysicalPrimaryQkRelativeBudget
    {Input Output Scalar : Set}
    (dataSet : PhysicalPrimaryQkSchurAssembly Input Output Scalar) : Set₁ where
  field
    oneEighth previousNormSquared : Scalar
    relativeProductBudget :
      Primary.LessEqual (additive dataSet)
        (multiply dataSet
          (Primary.uniformBudget (primalRows dataSet))
          (Adjoint.uniformColumnBudget (adjointColumns dataSet)))
        (multiply dataSet oneEighth previousNormSquared)

open PhysicalPrimaryQkRelativeBudget public

asPrimaryQkRelativeOneEighthBudget :
  ∀ {Input Output Scalar : Set}
    {dataSet : PhysicalPrimaryQkSchurAssembly Input Output Scalar} →
  PhysicalPrimaryQkRelativeBudget dataSet →
  Bridge.PrimaryQkRelativeOneEighthBudget
    (asStrongPrimaryQkSchurData dataSet)
asPrimaryQkRelativeOneEighthBudget budget = record
  { oneEighth = oneEighth budget
  ; previousNormSquared = previousNormSquared budget
  ; rowColumnProductBelowRelativeBudget = relativeProductBudget budget
  }

physicalPrimaryQkRelativeOneEighth :
  ∀ {Input Output Scalar : Set}
    {dataSet : PhysicalPrimaryQkSchurAssembly Input Output Scalar} →
  (budget : PhysicalPrimaryQkRelativeBudget dataSet) →
  Primary.LessEqual (additive dataSet)
    (operatorNormSquared dataSet)
    (multiply dataSet
      (oneEighth budget)
      (previousNormSquared budget))
physicalPrimaryQkRelativeOneEighth budget =
  Bridge.primaryQkSchurImpliesRelativeOneEighth
    (asPrimaryQkRelativeOneEighthBudget budget)

primaryQkPhysicalSchurAssemblyLevel : ProofLevel
primaryQkPhysicalSchurAssemblyLevel = machineChecked

primaryQkPhysicalRelativeContractionLevel : ProofLevel
primaryQkPhysicalRelativeContractionLevel = machineChecked

physicalQkPrimalSupportEnumerationInputsLevel : ProofLevel
physicalQkPrimalSupportEnumerationInputsLevel = conditional

physicalQkAdjointIncidenceEnumerationInputsLevel : ProofLevel
physicalQkAdjointIncidenceEnumerationInputsLevel = conditional

physicalQkNormalizedSchurBudgetInputsLevel : ProofLevel
physicalQkNormalizedSchurBudgetInputsLevel = conditional
