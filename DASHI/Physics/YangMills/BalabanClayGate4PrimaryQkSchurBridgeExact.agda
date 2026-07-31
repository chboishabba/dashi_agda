module DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkSchurBridgeExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4FiniteKernelSchurBlockAdjointExact as Schur

------------------------------------------------------------------------
-- This module is the exact attachment point between Balaban's primary Q_k
-- kernel statement and DASHI's finite Schur reduction.
--
-- The primary paper supplies locality and a pointwise kernel bound. The sibling
-- module converts those facts plus finite support cardinality into row sums.
-- The present module requires a separately identified adjoint-column family and
-- an explicit product budget. It does not derive a 1/8 contraction from the
-- coefficient L^{-d} in the averaging formula.
------------------------------------------------------------------------

record StrongPrimaryQkSchurData
    (Input Output Scalar : Set) : Set₁ where
  field
    additive : Primary.OrderedAdditiveScale Scalar
    multiply : Scalar → Scalar → Scalar

    rowKernel : Primary.UniformFiniteKernelBudget
      Output Input Scalar additive
    columnKernel : Primary.UniformFiniteKernelBudget
      Input Output Scalar additive

    -- The column data must be the absolute kernel of the actual adjoint, not an
    -- unrelated family with a convenient numerical bound.
    columnIsAdjointTranspose : ∀ (input : Input) (output : Output) →
      Primary.kernelAbsoluteValue
        (Primary.rowData columnKernel) input output
      ≡ Primary.kernelAbsoluteValue
          (Primary.rowData rowKernel) output input

    operatorNormSquared : Scalar
    finiteSchurTest :
      Primary.LessEqual additive operatorNormSquared
        (multiply
          (Primary.uniformBudget rowKernel)
          (Primary.uniformBudget columnKernel))

open StrongPrimaryQkSchurData public

primaryStrongRowSumBound :
  ∀ {Input Output Scalar : Set}
    (dataSet : StrongPrimaryQkSchurData Input Output Scalar)
    (output : Output) →
  Primary.LessEqual (additive dataSet)
    (Primary.finiteSum (additive dataSet)
      (Primary.localKernelValues
        (Primary.rowData (rowKernel dataSet)) output))
    (Primary.uniformBudget (rowKernel dataSet))
primaryStrongRowSumBound dataSet =
  Primary.primaryQkEveryLocalRowBelowUniformBudget (rowKernel dataSet)

primaryStrongColumnSumBound :
  ∀ {Input Output Scalar : Set}
    (dataSet : StrongPrimaryQkSchurData Input Output Scalar)
    (input : Input) →
  Primary.LessEqual (additive dataSet)
    (Primary.finiteSum (additive dataSet)
      (Primary.localKernelValues
        (Primary.rowData (columnKernel dataSet)) input))
    (Primary.uniformBudget (columnKernel dataSet))
primaryStrongColumnSumBound dataSet =
  Primary.primaryQkEveryLocalRowBelowUniformBudget (columnKernel dataSet)

asFiniteKernelSchurData :
  ∀ {Input Output Scalar : Set} →
  StrongPrimaryQkSchurData Input Output Scalar →
  Schur.FiniteKernelSchurData Input Output Scalar
asFiniteKernelSchurData {Input = Input} {Output = Output} dataSet = record
  { Kernel = Output → Input → Scalar
  ; selectedKernel =
      Primary.kernelAbsoluteValue
        (Primary.rowData (rowKernel dataSet))
  ; rowBound = Primary.uniformBudget (rowKernel dataSet)
  ; columnBound = Primary.uniformBudget (columnKernel dataSet)
  ; operatorNormSquared = operatorNormSquared dataSet
  ; multiply = multiply dataSet
  ; LessEqual = Primary.LessEqual (additive dataSet)
  ; transitive = Primary.transitive (additive dataSet)
  ; finiteRowKernelSumBound = ∀ (output : Output) →
      Primary.LessEqual (additive dataSet)
        (Primary.finiteSum (additive dataSet)
          (Primary.localKernelValues
            (Primary.rowData (rowKernel dataSet)) output))
        (Primary.uniformBudget (rowKernel dataSet))
  ; finiteColumnKernelSumBound = ∀ (input : Input) →
      Primary.LessEqual (additive dataSet)
        (Primary.finiteSum (additive dataSet)
          (Primary.localKernelValues
            (Primary.rowData (columnKernel dataSet)) input))
        (Primary.uniformBudget (columnKernel dataSet))
  ; finiteSchurTest = finiteSchurTest dataSet
  }

record PrimaryQkRelativeOneEighthBudget
    {Input Output Scalar : Set}
    (dataSet : StrongPrimaryQkSchurData Input Output Scalar) : Set₁ where
  field
    oneEighth previousNormSquared : Scalar
    rowColumnProductBelowRelativeBudget :
      Primary.LessEqual (additive dataSet)
        (multiply dataSet
          (Primary.uniformBudget (rowKernel dataSet))
          (Primary.uniformBudget (columnKernel dataSet)))
        (multiply dataSet oneEighth previousNormSquared)

open PrimaryQkRelativeOneEighthBudget public

asDyadicBlockAdjointSchurBudget :
  ∀ {Input Output Scalar : Set}
    {dataSet : StrongPrimaryQkSchurData Input Output Scalar} →
  PrimaryQkRelativeOneEighthBudget dataSet →
  Schur.DyadicBlockAdjointSchurBudget (asFiniteKernelSchurData dataSet)
asDyadicBlockAdjointSchurBudget budget = record
  { oneEighth = oneEighth budget
  ; previousNormSquared = previousNormSquared budget
  ; rowColumnProductBelowRelativeBudget =
      rowColumnProductBelowRelativeBudget budget
  }

primaryQkSchurImpliesRelativeOneEighth :
  ∀ {Input Output Scalar : Set}
    {dataSet : StrongPrimaryQkSchurData Input Output Scalar} →
  (budget : PrimaryQkRelativeOneEighthBudget dataSet) →
  Primary.LessEqual (additive dataSet)
    (operatorNormSquared dataSet)
    (multiply dataSet
      (oneEighth budget)
      (previousNormSquared budget))
primaryQkSchurImpliesRelativeOneEighth budget =
  Schur.finiteSchurImpliesRelativeOneEighthSquaredNorm
    (asDyadicBlockAdjointSchurBudget budget)

primaryQkPointwiseToStrongSchurRowsLevel : ProofLevel
primaryQkPointwiseToStrongSchurRowsLevel = machineChecked

primaryQkStrongSchurAdapterLevel : ProofLevel
primaryQkStrongSchurAdapterLevel = machineChecked

primaryQkRelativeOneEighthAssemblyLevel : ProofLevel
primaryQkRelativeOneEighthAssemblyLevel = machineChecked

physicalQkAdjointTransposeMeaningInputsLevel : ProofLevel
physicalQkAdjointTransposeMeaningInputsLevel = conditional

physicalQkRowColumnProductBudgetInputsLevel : ProofLevel
physicalQkRowColumnProductBudgetInputsLevel = conditional
