module DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary

------------------------------------------------------------------------
-- For a finite matrix kernel, the adjoint kernel is the transpose/conjugate
-- transpose of the primal kernel. After taking the selected absolute matrix
-- norm, the entry bound from Balaban's equation (147) therefore transports to
-- the adjoint columns. The new physical/combinatorial input is only the column
-- support incidence count.
------------------------------------------------------------------------

record PrimaryQkAdjointColumnMeaning
    (CoarseBond FineBond Scalar : Set)
    (algebra : Primary.OrderedAdditiveScale Scalar) : Set₁ where
  field
    primalRows : Primary.BalabanPrimaryQkRowData
      CoarseBond FineBond Scalar algebra

    adjointKernelAbsoluteValue : FineBond → CoarseBond → Scalar
    adjointTransposeExact :
      ∀ (fine : FineBond) (coarse : CoarseBond) →
      adjointKernelAbsoluteValue fine coarse
      ≡ Primary.kernelAbsoluteValue primalRows coarse fine

    columnSupport : FineBond → List CoarseBond
    columnBudget : FineBond → Scalar

    columnSupportCardinalityBudget : ∀ (fine : FineBond) →
      Primary.LessEqual algebra
        (Primary.natScale algebra
          (Primary.listLength (columnSupport fine))
          (Primary.primaryEntryBound primalRows))
        (columnBudget fine)

open PrimaryQkAdjointColumnMeaning public

asAdjointColumnRowData :
  ∀ {CoarseBond FineBond Scalar : Set}
    {algebra : Primary.OrderedAdditiveScale Scalar} →
  PrimaryQkAdjointColumnMeaning
    CoarseBond FineBond Scalar algebra →
  Primary.BalabanPrimaryQkRowData
    FineBond CoarseBond Scalar algebra
asAdjointColumnRowData {algebra = algebra} meaning = record
  { kernelAbsoluteValue = adjointKernelAbsoluteValue meaning
  ; localSupport = columnSupport meaning
  ; primaryEntryBound = Primary.primaryEntryBound (primalRows meaning)
  ; rowBudget = columnBudget meaning
  ; proposition4PointwiseBound = λ fine coarse →
      subst
        (λ value → Primary.LessEqual algebra
          value (Primary.primaryEntryBound (primalRows meaning)))
        (sym (adjointTransposeExact meaning fine coarse))
        (Primary.proposition4PointwiseBound
          (primalRows meaning) coarse fine)
  ; localSupportCardinalityBudget = columnSupportCardinalityBudget meaning
  }

record UniformPrimaryQkAdjointColumnBudget
    (CoarseBond FineBond Scalar : Set)
    (algebra : Primary.OrderedAdditiveScale Scalar) : Set₁ where
  field
    adjointMeaning : PrimaryQkAdjointColumnMeaning
      CoarseBond FineBond Scalar algebra
    uniformColumnBudget : Scalar
    everyColumnBudgetUniform : ∀ (fine : FineBond) →
      Primary.LessEqual algebra
        (columnBudget adjointMeaning fine)
        uniformColumnBudget

open UniformPrimaryQkAdjointColumnBudget public

asUniformAdjointColumnKernelBudget :
  ∀ {CoarseBond FineBond Scalar : Set}
    {algebra : Primary.OrderedAdditiveScale Scalar} →
  UniformPrimaryQkAdjointColumnBudget
    CoarseBond FineBond Scalar algebra →
  Primary.UniformFiniteKernelBudget
    FineBond CoarseBond Scalar algebra
asUniformAdjointColumnKernelBudget dataSet = record
  { rowData = asAdjointColumnRowData (adjointMeaning dataSet)
  ; uniformBudget = uniformColumnBudget dataSet
  ; everyRowBudgetUniform = everyColumnBudgetUniform dataSet
  }

primaryQkAdjointColumnSumBelowUniformBudget :
  ∀ {CoarseBond FineBond Scalar : Set}
    {algebra : Primary.OrderedAdditiveScale Scalar}
    (dataSet : UniformPrimaryQkAdjointColumnBudget
      CoarseBond FineBond Scalar algebra)
    (fine : FineBond) →
  Primary.LessEqual algebra
    (Primary.finiteSum algebra
      (Primary.localKernelValues
        (asAdjointColumnRowData (adjointMeaning dataSet)) fine))
    (uniformColumnBudget dataSet)
primaryQkAdjointColumnSumBelowUniformBudget dataSet =
  Primary.primaryQkEveryLocalRowBelowUniformBudget
    (asUniformAdjointColumnKernelBudget dataSet)

adjointEntryBoundFromPrimaryTransposeLevel : ProofLevel
adjointEntryBoundFromPrimaryTransposeLevel = machineChecked

adjointColumnFiniteSumLevel : ProofLevel
adjointColumnFiniteSumLevel = machineChecked

physicalQkAdjointTransposeIdentificationInputsLevel : ProofLevel
physicalQkAdjointTransposeIdentificationInputsLevel = conditional

physicalQkColumnIncidenceCardinalityInputsLevel : ProofLevel
physicalQkColumnIncidenceCardinalityInputsLevel = conditional
