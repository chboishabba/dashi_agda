module DASHI.Physics.YangMills.BalabanClayGate4CMP109ConstantWeightSchurExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkAdjointColumnExact as Adjoint
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkPrimaryKernelInstantiationExact as Periodic

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
-- constant at a fixed scale.  The finite algebra below proves
--
--   rowWeighted(c)    = rowUnweighted(c) * q,
--   columnWeighted(b) = p * columnUnweighted(b).
--
-- The physical weighted estimates therefore reduce to two scalar comparisons
-- between the volume weights and the existing uniform support/entry budgets.
------------------------------------------------------------------------

record OrderedDistributiveWeightAlgebra
    (Scalar : Set)
    (additive : Primary.OrderedAdditiveScale Scalar) : Set₁ where
  field
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
  ∀ {Scalar additive}
    (algebra : OrderedDistributiveWeightAlgebra Scalar additive)
    (weight : Scalar) (values : List Scalar) →
  Primary.finiteSum additive
    (mapList (λ value → multiply algebra value weight) values)
  ≡ multiply algebra (Primary.finiteSum additive values) weight
finiteSumRightScale algebra weight [] =
  sym (multiplyZeroLeft algebra weight)
finiteSumRightScale {additive = additive} algebra weight
    (value ∷ values) =
  trans
    (cong
      (Primary.add additive (multiply algebra value weight))
      (finiteSumRightScale algebra weight values))
    (sym (rightDistributes algebra value
      (Primary.finiteSum additive values) weight))

finiteSumLeftScale :
  ∀ {Scalar additive}
    (algebra : OrderedDistributiveWeightAlgebra Scalar additive)
    (weight : Scalar) (values : List Scalar) →
  Primary.finiteSum additive
    (mapList (λ value → multiply algebra weight value) values)
  ≡ multiply algebra weight (Primary.finiteSum additive values)
finiteSumLeftScale algebra weight [] =
  sym (multiplyZeroRight algebra weight)
finiteSumLeftScale {additive = additive} algebra weight
    (value ∷ values) =
  trans
    (cong
      (Primary.add additive (multiply algebra weight value))
      (finiteSumLeftScale algebra weight values))
    (sym (leftDistributes algebra weight value
      (Primary.finiteSum additive values)))

record CMP109ConstantWeightSchurInputs
    (CoarseBond FineBond Scalar : Set) : Set₁ where
  field
    primary : Periodic.PeriodicPrimaryQkKernelInputs
      CoarseBond FineBond Scalar

    weightAlgebra : OrderedDistributiveWeightAlgebra
      Scalar (Periodic.algebra primary)

    fineWeight coarseWeight : Scalar
    alpha beta operatorNormSquared : Scalar

    FineWeightPositive CoarseWeightPositive : Scalar → Set
    fineWeightPositive : FineWeightPositive fineWeight
    coarseWeightPositive : CoarseWeightPositive coarseWeight

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

rowKernelValues :
  ∀ {CoarseBond FineBond Scalar} →
  CMP109ConstantWeightSchurInputs CoarseBond FineBond Scalar →
  CoarseBond → List Scalar
rowKernelValues inputs coarse =
  Primary.localKernelValues
    (Periodic.periodicPrimaryRowData (primary inputs)) coarse

columnKernelValues :
  ∀ {CoarseBond FineBond Scalar} →
  CMP109ConstantWeightSchurInputs CoarseBond FineBond Scalar →
  FineBond → List Scalar
columnKernelValues inputs fine =
  Primary.localKernelValues
    (Adjoint.asAdjointColumnRowData
      (Adjoint.adjointMeaning
        (Periodic.periodicUniformPrimaryAdjointColumns
          (primary inputs))))
    fine

constantWeightedRowSum :
  ∀ {CoarseBond FineBond Scalar} →
  CMP109ConstantWeightSchurInputs CoarseBond FineBond Scalar →
  CoarseBond → Scalar
constantWeightedRowSum inputs coarse =
  Primary.finiteSum (Periodic.algebra (primary inputs))
    (mapList
      (λ value → multiply (weightAlgebra inputs)
        value (fineWeight inputs))
      (rowKernelValues inputs coarse))

constantWeightedColumnSum :
  ∀ {CoarseBond FineBond Scalar} →
  CMP109ConstantWeightSchurInputs CoarseBond FineBond Scalar →
  FineBond → Scalar
constantWeightedColumnSum inputs fine =
  Primary.finiteSum (Periodic.algebra (primary inputs))
    (mapList
      (λ value → multiply (weightAlgebra inputs)
        (coarseWeight inputs) value)
      (columnKernelValues inputs fine))

constantWeightedRowSumFactors :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar)
    coarse →
  constantWeightedRowSum inputs coarse
  ≡ multiply (weightAlgebra inputs)
      (Primary.finiteSum (Periodic.algebra (primary inputs))
        (rowKernelValues inputs coarse))
      (fineWeight inputs)
constantWeightedRowSumFactors inputs coarse =
  finiteSumRightScale (weightAlgebra inputs)
    (fineWeight inputs) (rowKernelValues inputs coarse)

constantWeightedColumnSumFactors :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar)
    fine →
  constantWeightedColumnSum inputs fine
  ≡ multiply (weightAlgebra inputs)
      (coarseWeight inputs)
      (Primary.finiteSum (Periodic.algebra (primary inputs))
        (columnKernelValues inputs fine))
constantWeightedColumnSumFactors inputs fine =
  finiteSumLeftScale (weightAlgebra inputs)
    (coarseWeight inputs) (columnKernelValues inputs fine)

constantWeightedRowBelowAlphaWeight :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar)
    coarse →
  Primary.LessEqual (Periodic.algebra (primary inputs))
    (constantWeightedRowSum inputs coarse)
    (multiply (weightAlgebra inputs)
      (alpha inputs) (coarseWeight inputs))
constantWeightedRowBelowAlphaWeight inputs coarse =
  subst
    (λ lower → Primary.LessEqual (Periodic.algebra (primary inputs))
      lower
      (multiply (weightAlgebra inputs)
        (alpha inputs) (coarseWeight inputs)))
    (sym (constantWeightedRowSumFactors inputs coarse))
    (Primary.transitive (Periodic.algebra (primary inputs))
      (multiplyMonotone (weightAlgebra inputs)
        (Primary.primaryQkEveryLocalRowBelowUniformBudget
          (Periodic.periodicUniformPrimaryRows (primary inputs)) coarse)
        (Primary.reflexive (Periodic.algebra (primary inputs))
          (fineWeight inputs)))
      (rowWeightBudget inputs))

constantWeightedColumnBelowBetaWeight :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar)
    fine →
  Primary.LessEqual (Periodic.algebra (primary inputs))
    (constantWeightedColumnSum inputs fine)
    (multiply (weightAlgebra inputs)
      (beta inputs) (fineWeight inputs))
constantWeightedColumnBelowBetaWeight inputs fine =
  subst
    (λ lower → Primary.LessEqual (Periodic.algebra (primary inputs))
      lower
      (multiply (weightAlgebra inputs)
        (beta inputs) (fineWeight inputs)))
    (sym (constantWeightedColumnSumFactors inputs fine))
    (Primary.transitive (Periodic.algebra (primary inputs))
      (multiplyMonotone (weightAlgebra inputs)
        (Primary.reflexive (Periodic.algebra (primary inputs))
          (coarseWeight inputs))
        (Adjoint.primaryQkAdjointColumnSumBelowUniformBudget
          (Periodic.periodicUniformPrimaryAdjointColumns
            (primary inputs)) fine))
      (columnWeightBudget inputs))

constantWeightRelativeOneEighth :
  ∀ {CoarseBond FineBond Scalar}
    (inputs : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar) →
  Primary.LessEqual (Periodic.algebra (primary inputs))
    (operatorNormSquared inputs)
    (multiply (weightAlgebra inputs)
      (oneEighth inputs) (previousNormSquared inputs))
constantWeightRelativeOneEighth inputs =
  Primary.transitive (Periodic.algebra (primary inputs))
    (finiteWeightedSchurTest inputs)
    (weightedProductBelowRelativeBudget inputs)

record LiteralPeriodicConstantWeightAgreement
    (CoarseBond FineBond Scalar : Set) : Set₁ where
  field
    constantWeights : CMP109ConstantWeightSchurInputs
      CoarseBond FineBond Scalar

    literalPeriodicWeightedRowSum : CoarseBond → Scalar
    literalPeriodicWeightedColumnSum : FineBond → Scalar

    rowSumMeaning : ∀ coarse →
      literalPeriodicWeightedRowSum coarse
      ≡ constantWeightedRowSum constantWeights coarse

    columnSumMeaning : ∀ fine →
      literalPeriodicWeightedColumnSum fine
      ≡ constantWeightedColumnSum constantWeights fine

open LiteralPeriodicConstantWeightAgreement public

cmp109ConstantWeightFactorizationLevel : ProofLevel
cmp109ConstantWeightFactorizationLevel = machineChecked

cmp109ConstantWeightRowColumnBudgetLevel : ProofLevel
cmp109ConstantWeightRowColumnBudgetLevel = machineChecked

cmp109ConstantWeightRelativeContractionLevel : ProofLevel
cmp109ConstantWeightRelativeContractionLevel = machineChecked

physicalCMP109FineCoarseCellWeightInputsLevel : ProofLevel
physicalCMP109FineCoarseCellWeightInputsLevel = conditional

physicalCMP109ConstantWeightScalarBudgetInputsLevel : ProofLevel
physicalCMP109ConstantWeightScalarBudgetInputsLevel = conditional

physicalPeriodicLiteralWeightedSumIdentificationInputsLevel : ProofLevel
physicalPeriodicLiteralWeightedSumIdentificationInputsLevel = conditional
