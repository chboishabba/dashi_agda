module DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkPrimaryKernelInstantiationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact as Adjoint
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkUniformSupportBoundsExact as Uniform

------------------------------------------------------------------------
-- Exact bridge from executable periodic support counts to the primary Q_k
-- finite-kernel budgets.
--
-- The remaining physical inputs are now sharply separated:
--   * the decidable support predicate is the selected endpoint-block union;
--   * the kernel is the derivative of the selected averaging convention;
--   * Proposition 4 supplies the pointwise entry bound;
--   * natural-count scaling is monotone for the selected nonnegative scalar.
------------------------------------------------------------------------

listLengthAgreement :
  ∀ {A : Set} (values : List A) →
  Primary.listLength values ≡ Support.listLength values
listLengthAgreement [] = refl
listLengthAgreement (_ ∷ values)
  rewrite listLengthAgreement values = refl

record PeriodicPrimaryQkKernelInputs
    (CoarseBond FineBond Scalar : Set) : Set₁ where
  field
    supportData : Support.FiniteKernelSupportRelation CoarseBond FineBond
    algebra : Primary.OrderedAdditiveScale Scalar

    kernelAbsoluteValue : CoarseBond → FineBond → Scalar
    primaryEntryBound : Scalar

    proposition4PointwiseBound : ∀ coarse fine →
      Primary.LessEqual algebra
        (kernelAbsoluteValue coarse fine)
        primaryEntryBound

    natScaleMonotone : ∀ {lower upper} →
      Uniform._≤ᴺ_ lower upper →
      Primary.LessEqual algebra
        (Primary.natScale algebra lower primaryEntryBound)
        (Primary.natScale algebra upper primaryEntryBound)

    adjointKernelAbsoluteValue : FineBond → CoarseBond → Scalar
    adjointTransposeExact : ∀ fine coarse →
      adjointKernelAbsoluteValue fine coarse
      ≡ kernelAbsoluteValue coarse fine

open PeriodicPrimaryQkKernelInputs public

periodicPrimaryRowData :
  ∀ {CoarseBond FineBond Scalar : Set}
    (dataSet : PeriodicPrimaryQkKernelInputs CoarseBond FineBond Scalar) →
  Primary.BalabanPrimaryQkRowData
    CoarseBond FineBond Scalar (algebra dataSet)
periodicPrimaryRowData dataSet = record
  { kernelAbsoluteValue = kernelAbsoluteValue dataSet
  ; localSupport = Support.rowSupport (supportData dataSet)
  ; primaryEntryBound = primaryEntryBound dataSet
  ; rowBudget = λ coarse →
      Primary.natScale (algebra dataSet)
        (Uniform.uniformRowBound (supportData dataSet))
        (primaryEntryBound dataSet)
  ; proposition4PointwiseBound = proposition4PointwiseBound dataSet
  ; localSupportCardinalityBudget = λ coarse →
      subst
        (λ count → Primary.LessEqual (algebra dataSet)
          (Primary.natScale (algebra dataSet) count
            (primaryEntryBound dataSet))
          (Primary.natScale (algebra dataSet)
            (Uniform.uniformRowBound (supportData dataSet))
            (primaryEntryBound dataSet)))
        (sym
          (listLengthAgreement
            (Support.rowSupport (supportData dataSet) coarse)))
        (natScaleMonotone dataSet
          (Uniform.rowCountBelowUniformBound
            (supportData dataSet) coarse))
  }

periodicUniformPrimaryRows :
  ∀ {CoarseBond FineBond Scalar : Set}
    (dataSet : PeriodicPrimaryQkKernelInputs CoarseBond FineBond Scalar) →
  Primary.UniformFiniteKernelBudget
    CoarseBond FineBond Scalar (algebra dataSet)
periodicUniformPrimaryRows dataSet = record
  { rowData = periodicPrimaryRowData dataSet
  ; uniformBudget =
      Primary.natScale (algebra dataSet)
        (Uniform.uniformRowBound (supportData dataSet))
        (primaryEntryBound dataSet)
  ; everyRowBudgetUniform = λ coarse →
      Primary.reflexive (algebra dataSet)
        (Primary.natScale (algebra dataSet)
          (Uniform.uniformRowBound (supportData dataSet))
          (primaryEntryBound dataSet))
  }

periodicPrimaryAdjointMeaning :
  ∀ {CoarseBond FineBond Scalar : Set}
    (dataSet : PeriodicPrimaryQkKernelInputs CoarseBond FineBond Scalar) →
  Adjoint.PrimaryQkAdjointColumnMeaning
    CoarseBond FineBond Scalar (algebra dataSet)
periodicPrimaryAdjointMeaning dataSet = record
  { primalRows = periodicPrimaryRowData dataSet
  ; adjointKernelAbsoluteValue = adjointKernelAbsoluteValue dataSet
  ; adjointTransposeExact = adjointTransposeExact dataSet
  ; columnSupport = Support.columnIncidence (supportData dataSet)
  ; columnBudget = λ fine →
      Primary.natScale (algebra dataSet)
        (Uniform.uniformColumnBound (supportData dataSet))
        (primaryEntryBound dataSet)
  ; columnSupportCardinalityBudget = λ fine →
      subst
        (λ count → Primary.LessEqual (algebra dataSet)
          (Primary.natScale (algebra dataSet) count
            (primaryEntryBound dataSet))
          (Primary.natScale (algebra dataSet)
            (Uniform.uniformColumnBound (supportData dataSet))
            (primaryEntryBound dataSet)))
        (sym
          (listLengthAgreement
            (Support.columnIncidence (supportData dataSet) fine)))
        (natScaleMonotone dataSet
          (Uniform.columnCountBelowUniformBound
            (supportData dataSet) fine))
  }

periodicUniformPrimaryAdjointColumns :
  ∀ {CoarseBond FineBond Scalar : Set}
    (dataSet : PeriodicPrimaryQkKernelInputs CoarseBond FineBond Scalar) →
  Adjoint.UniformPrimaryQkAdjointColumnBudget
    CoarseBond FineBond Scalar (algebra dataSet)
periodicUniformPrimaryAdjointColumns dataSet = record
  { adjointMeaning = periodicPrimaryAdjointMeaning dataSet
  ; uniformColumnBudget =
      Primary.natScale (algebra dataSet)
        (Uniform.uniformColumnBound (supportData dataSet))
        (primaryEntryBound dataSet)
  ; everyColumnBudgetUniform = λ fine →
      Primary.reflexive (algebra dataSet)
        (Primary.natScale (algebra dataSet)
          (Uniform.uniformColumnBound (supportData dataSet))
          (primaryEntryBound dataSet))
  }

periodicPrimaryRowBudgetInstantiationLevel : ProofLevel
periodicPrimaryRowBudgetInstantiationLevel = machineChecked

periodicPrimaryAdjointColumnBudgetInstantiationLevel : ProofLevel
periodicPrimaryAdjointColumnBudgetInstantiationLevel = machineChecked

physicalSupportPredicateAndKernelIdentificationInputsLevel : ProofLevel
physicalSupportPredicateAndKernelIdentificationInputsLevel = conditional

physicalEntryBoundCountMonotonicityInputsLevel : ProofLevel
physicalEntryBoundCountMonotonicityInputsLevel = conditional
