module DASHI.Physics.YangMills.BalabanClayGate4CMP109ConstantWeightSchurExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact as Adjoint
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkPrimaryKernelInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkWeightedSchurInstantiationExact as WeightedPeriodic

------------------------------------------------------------------------
-- Translation-invariant physical weights.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- On a periodic homogeneous lattice the fine- and coarse-bond cell weights are
-- constant at a fixed scale.  The finite algebra below proves that the literal
-- weighted row and column sums factor as
--
--   rowWeighted(c)    = rowUnweighted(c) * q,
--   columnWeighted(b) = p * columnUnweighted(b).
--
-- Thus the physical weighted estimates reduce to two scalar comparisons between
-- the volume weights and the existing uniform support/entry budgets.
------------------------------------------------------------------------

record OrderedDistributiveWeightAlgebra (Scalar : Set) : Set₁ where
  field
    additive : Primary.OrderedAdditiveScale Scalar
    multiply : Scalar → Scalar → Scalar

    multiplyMonotone : ∀ {left lower right upper} →
      Primary.LessEqual additive left lower →
      Primary.LessEqual additive right upper →
      Primary.LessEqual additive
        (multiply left right) (multiply lower upper)

    multiplyZeroLeft : ∀ value →
      multiply (Primary.zeroScalar additive) value
      ≡ Primary.zeroScalar additive

    multiplyZeroRight : ∀ value →
      multiply value (Primary.zeroScalar additive)
      ≡ Primary.zeroScalar additive

    leftDistributes : ∀ left middle right →
      multiply left (Primary.add additive middle right)
      ≡ Primary.add additive
          (multiply left middle) (multiply left right)

    rightDistributes : ∀ left middle right →
      multiply (Primary.add additive left middle) right
      ≡ Primary.add additive
          (multiply left right) (multiply middle right)

open OrderedDistributiveWeightAlgebra public

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

finiteSumRightScale :
  ∀ {Scalar}
    (algebra : OrderedDistributiveWeightAlgebra Scalar)
    (weight : Scalar) (values : List Scalar) →
  Primary.finiteSum (additive algebra)
    (mapList (λ value → multiply algebra value weight) values)
  ≡ multiply algebra
      (Primary.finiteSum (additive algebra) values) weight
finiteSumRightScale algebra weight [] =
  sym (multiplyZeroLeft algebra weight)
finiteSumRightScale algebra weight (value ∷ values) =
  trans
    (cong
      (Primary.add (additive algebra)
        (multiply algebra value weight))
      (finiteSumRightScale algebra weight values))
    (sym (rightDistributes algebra value
      (Primary.finiteSum (additive algebra) values) weight))

finiteSumLeftScale :
  ∀ {Scalar}
    (algebra : OrderedDistributiveWeightAlgebra Scalar)
    (weight : Scalar) (values : List Scalar) →
  Primary.finiteSum (additive algebra)
    (mapList (λ value → multiply algebra weight value) values)
  ≡ multiply algebra weight
      (Primary.finiteSum (additive algebra) values)
finiteSumLeftScale algebra weight [] =
  sym (multiplyZeroRight algebra weight)
finiteSumLeftScale algebra weight (value ∷ values) =
  trans
    (cong
      (Primary.add (additive algebra)
        (multiply algebra weight value))
      (finiteSumLeftScale algebra weight values))
    (sym (leftDistributes algebra weight value
      (Primary.finiteSum (additive algebra) values)))

record CMP109ConstantWeightSchurInputs
    (CoarseBond FineBond Scalar : Set) : Set₁ where
  field
    primary : Periodic.PeriodicPrimaryQkKernelInputs
      CoarseBond FineBond Scalar

    weightAlgebra : OrderedDistributiveWeightAlgebra Scalar

    additiveAgreement :
      additive weightAlgebra ≡ Periodic.algebra primary

    fineWeight coarseWeight : Scalar

    FineWeightPositive : Scalar → Set
    CoarseWeightPositive : Scalar → Set
    fineWeightPositive : FineWeightPositive fineWeight
    coarseWeightPositive : CoarseWeightPositive coarseWeight

    alpha beta operatorNormSquared : Scalar

    rowWeightBudget :
      Primary.LessEqual (Periodic.algebra primary)
        (multiply weightAlgebra
          (Primary.uniformBudget
            (Periodic.periodicUniformPrimaryRows primary))
          fineWeight)
        (multiply weightAlgebra alpha coarseWeight)

    columnWeightBudget :
      Primary.LessEqual (Periodic.algebra primary)
        (multiply weightAlgebra coarseWeight
          (Adjoint.uniformColumnBudget
            (Periodic.periodicUniformPrimaryAdjointColumns primary)))
        (multiply weightAlgebra beta fineWeight)

    finiteWeightedSchurTest :
      Primary.LessEqual (Periodic.algebra primary)
        operatorNormSquared (multiply weightAlgebra alpha beta)

    oneEighth previousNormSquared : Scalar

    weightedProductBelowRelativeBudget :
      Primary.LessEqual (Periodic.algebra primary)
        (multiply weightAlgebra alpha beta)
        (multiply weightAlgebra oneEighth previousNormSquared)

open CMP109ConstantWeightSchurInputs public

constantWeightedRowBound :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar)
    coarse →
  Primary.LessEqual (Periodic.algebra (primary inputs))
    (Primary.finiteSum (Periodic.algebra (primary inputs))
      (mapList
        (λ fine → multiply (weightAlgebra inputs)
          (Periodic.kernelAbsoluteValue (primary inputs) coarse fine)
          (fineWeight inputs))
        (Support.rowSupport
          (Periodic.supportData (primary inputs)) coarse)))
    (multiply (weightAlgebra inputs)
      (alpha inputs) (coarseWeight inputs))
constantWeightedRowBound inputs coarse =
  subst
    (λ selectedAdditive →
      Primary.LessEqual selectedAdditive
        (Primary.finiteSum selectedAdditive
          (mapList
            (λ fine → multiply (weightAlgebra inputs)
              (Periodic.kernelAbsoluteValue (primary inputs) coarse fine)
              (fineWeight inputs))
            (Support.rowSupport
              (Periodic.supportData (primary inputs)) coarse)))
        (multiply (weightAlgebra inputs)
          (alpha inputs) (coarseWeight inputs)))
    (additiveAgreement inputs)
    (subst
      (λ lower →
        Primary.LessEqual (additive (weightAlgebra inputs)) lower
          (multiply (weightAlgebra inputs)
            (alpha inputs) (coarseWeight inputs)))
      (sym
        (finiteSumRightScale (weightAlgebra inputs)
          (fineWeight inputs)
          (Primary.localKernelValues
            (Periodic.periodicPrimaryRowData (primary inputs)) coarse)))
      (Primary.transitive (additive (weightAlgebra inputs))
        (multiplyMonotone (weightAlgebra inputs)
          (Primary.primaryQkEveryLocalRowBelowUniformBudget
            (Periodic.periodicUniformPrimaryRows (primary inputs)) coarse)
          (Primary.reflexive (additive (weightAlgebra inputs))
            (fineWeight inputs)))
        (subst
          (λ relation → relation)
          (cong
            (λ selectedAdditive →
              Primary.LessEqual selectedAdditive
                (multiply (weightAlgebra inputs)
                  (Primary.uniformBudget
                    (Periodic.periodicUniformPrimaryRows (primary inputs)))
                  (fineWeight inputs))
                (multiply (weightAlgebra inputs)
                  (alpha inputs) (coarseWeight inputs)))
            (sym (additiveAgreement inputs)))
          (rowWeightBudget inputs))))

constantWeightedColumnBound :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar)
    fine →
  Primary.LessEqual (Periodic.algebra (primary inputs))
    (Primary.finiteSum (Periodic.algebra (primary inputs))
      (mapList
        (λ coarse → multiply (weightAlgebra inputs)
          (coarseWeight inputs)
          (Periodic.kernelAbsoluteValue (primary inputs) coarse fine))
        (Support.columnIncidence
          (Periodic.supportData (primary inputs)) fine)))
    (multiply (weightAlgebra inputs)
      (beta inputs) (fineWeight inputs))
constantWeightedColumnBound inputs fine =
  subst
    (λ selectedAdditive →
      Primary.LessEqual selectedAdditive
        (Primary.finiteSum selectedAdditive
          (mapList
            (λ coarse → multiply (weightAlgebra inputs)
              (coarseWeight inputs)
              (Periodic.kernelAbsoluteValue (primary inputs) coarse fine))
            (Support.columnIncidence
              (Periodic.supportData (primary inputs)) fine)))
        (multiply (weightAlgebra inputs)
          (beta inputs) (fineWeight inputs)))
    (additiveAgreement inputs)
    (subst
      (λ lower →
        Primary.LessEqual (additive (weightAlgebra inputs)) lower
          (multiply (weightAlgebra inputs)
            (beta inputs) (fineWeight inputs)))
      (sym
        (finiteSumLeftScale (weightAlgebra inputs)
          (coarseWeight inputs)
          (Primary.localKernelValues
            (Adjoint.asAdjointColumnRowData
              (Adjoint.adjointMeaning
                (Periodic.periodicUniformPrimaryAdjointColumns
                  (primary inputs))))
            fine)))
      (Primary.transitive (additive (weightAlgebra inputs))
        (multiplyMonotone (weightAlgebra inputs)
          (Primary.reflexive (additive (weightAlgebra inputs))
            (coarseWeight inputs))
          (Adjoint.primaryQkAdjointColumnSumBelowUniformBudget
            (Periodic.periodicUniformPrimaryAdjointColumns
              (primary inputs)) fine))
        (subst
          (λ relation → relation)
          (cong
            (λ selectedAdditive →
              Primary.LessEqual selectedAdditive
                (multiply (weightAlgebra inputs)
                  (coarseWeight inputs)
                  (Adjoint.uniformColumnBudget
                    (Periodic.periodicUniformPrimaryAdjointColumns
                      (primary inputs))))
                (multiply (weightAlgebra inputs)
                  (beta inputs) (fineWeight inputs)))
            (sym (additiveAgreement inputs)))
          (columnWeightBudget inputs))))

asPeriodicPrimaryWeightedSchurInputs :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar) →
  WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs
    CoarseBond FineBond Scalar
asPeriodicPrimaryWeightedSchurInputs inputs = record
  { WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.primary =
      primary inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.multiply =
      multiply (weightAlgebra inputs)
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.inputWeight =
      λ fine → fineWeight inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.outputWeight =
      λ coarse → coarseWeight inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.InputWeightPositive =
      λ fine → FineWeightPositive inputs (fineWeight inputs)
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.OutputWeightPositive =
      λ coarse → CoarseWeightPositive inputs (coarseWeight inputs)
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.inputWeightPositive =
      λ fine → fineWeightPositive inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.outputWeightPositive =
      λ coarse → coarseWeightPositive inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.alpha = alpha inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.beta = beta inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.operatorNormSquared =
      operatorNormSquared inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.weightedRowBound =
      constantWeightedRowBound inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.weightedColumnBound =
      constantWeightedColumnBound inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.finiteWeightedSchurTest =
      finiteWeightedSchurTest inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.oneEighth =
      oneEighth inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.previousNormSquared =
      previousNormSquared inputs
  ; WeightedPeriodic.PeriodicPrimaryWeightedSchurInputs.weightedProductBelowRelativeBudget =
      weightedProductBelowRelativeBudget inputs
  }

cmp109ConstantWeightFactorizationLevel : ProofLevel
cmp109ConstantWeightFactorizationLevel = machineChecked

cmp109ConstantWeightRowColumnBudgetLevel : ProofLevel
cmp109ConstantWeightRowColumnBudgetLevel = machineChecked

cmp109ConstantWeightSchurInstantiationLevel : ProofLevel
cmp109ConstantWeightSchurInstantiationLevel = machineChecked

physicalCMP109FineCoarseCellWeightInputsLevel : ProofLevel
physicalCMP109FineCoarseCellWeightInputsLevel = conditional

physicalCMP109ConstantWeightScalarBudgetInputsLevel : ProofLevel
physicalCMP109ConstantWeightScalarBudgetInputsLevel = conditional
