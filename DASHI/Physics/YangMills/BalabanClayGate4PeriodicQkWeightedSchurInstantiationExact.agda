module DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkWeightedSchurInstantiationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkPrimaryKernelInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurBlockAdjointExact as Weighted
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkWeightedSchurExact as PrimaryWeighted

------------------------------------------------------------------------
-- Literal weighted sums on the executable periodic support lists.
--
-- For coarse bond c and fine bond b, the finite Schur sums are represented as
--
--   row(c)    = sum_{b in S(c)} |Q_k(c,b)| q(b),
--   column(b) = sum_{c : b in S(c)} p(c) |Q_k(c,b)|.
--
-- The support and incidence lists are computed by the periodic enumerator. This
-- module therefore removes the final representation ambiguity from the weighted
-- Schur interface. The analytic work that remains is to choose physical weights
-- p,q and prove the alpha, beta and relative-product inequalities.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) = function value ∷ mapList function values

record PeriodicPrimaryWeightedSchurInputs
    (CoarseBond FineBond Scalar : Set) : Set₁ where
  field
    primary : Periodic.PeriodicPrimaryQkKernelInputs
      CoarseBond FineBond Scalar

    multiply : Scalar → Scalar → Scalar
    inputWeight : FineBond → Scalar
    outputWeight : CoarseBond → Scalar

    InputWeightPositive : FineBond → Set
    OutputWeightPositive : CoarseBond → Set
    inputWeightPositive : ∀ fine → InputWeightPositive fine
    outputWeightPositive : ∀ coarse → OutputWeightPositive coarse

    alpha beta operatorNormSquared : Scalar

    weightedRowBound : ∀ coarse →
      Primary.LessEqual (Periodic.algebra primary)
        (Primary.finiteSum (Periodic.algebra primary)
          (mapList
            (λ fine → multiply
              (Periodic.kernelAbsoluteValue primary coarse fine)
              (inputWeight fine))
            (Support.rowSupport
              (Periodic.supportData primary) coarse)))
        (multiply alpha (outputWeight coarse))

    weightedColumnBound : ∀ fine →
      Primary.LessEqual (Periodic.algebra primary)
        (Primary.finiteSum (Periodic.algebra primary)
          (mapList
            (λ coarse → multiply
              (outputWeight coarse)
              (Periodic.kernelAbsoluteValue primary coarse fine))
            (Support.columnIncidence
              (Periodic.supportData primary) fine)))
        (multiply beta (inputWeight fine))

    finiteWeightedSchurTest :
      Primary.LessEqual (Periodic.algebra primary)
        operatorNormSquared (multiply alpha beta)

    oneEighth previousNormSquared : Scalar
    weightedProductBelowRelativeBudget :
      Primary.LessEqual (Periodic.algebra primary)
        (multiply alpha beta)
        (multiply oneEighth previousNormSquared)

open PeriodicPrimaryWeightedSchurInputs public

literalWeightedRowSum :
  ∀ {CoarseBond FineBond Scalar : Set} →
  PeriodicPrimaryWeightedSchurInputs CoarseBond FineBond Scalar →
  CoarseBond → Scalar
literalWeightedRowSum dataSet coarse =
  Primary.finiteSum (Periodic.algebra (primary dataSet))
    (mapList
      (λ fine → multiply dataSet
        (Periodic.kernelAbsoluteValue (primary dataSet) coarse fine)
        (inputWeight dataSet fine))
      (Support.rowSupport
        (Periodic.supportData (primary dataSet)) coarse))

literalWeightedColumnSum :
  ∀ {CoarseBond FineBond Scalar : Set} →
  PeriodicPrimaryWeightedSchurInputs CoarseBond FineBond Scalar →
  FineBond → Scalar
literalWeightedColumnSum dataSet fine =
  Primary.finiteSum (Periodic.algebra (primary dataSet))
    (mapList
      (λ coarse → multiply dataSet
        (outputWeight dataSet coarse)
        (Periodic.kernelAbsoluteValue (primary dataSet) coarse fine))
      (Support.columnIncidence
        (Periodic.supportData (primary dataSet)) fine))

asFiniteWeightedSchurData :
  ∀ {CoarseBond FineBond Scalar : Set} →
  PeriodicPrimaryWeightedSchurInputs CoarseBond FineBond Scalar →
  Weighted.FiniteWeightedSchurData FineBond CoarseBond Scalar
asFiniteWeightedSchurData dataSet = record
  { Kernel = Periodic.kernelAbsoluteValue (primary dataSet)
  ; inputWeight = inputWeight dataSet
  ; outputWeight = outputWeight dataSet
  ; weightedRowSum = literalWeightedRowSum dataSet
  ; weightedColumnSum = literalWeightedColumnSum dataSet
  ; alpha = alpha dataSet
  ; beta = beta dataSet
  ; operatorNormSquared = operatorNormSquared dataSet
  ; multiply = multiply dataSet
  ; LessEqual = Primary.LessEqual (Periodic.algebra (primary dataSet))
  ; transitive = Primary.transitive (Periodic.algebra (primary dataSet))
  ; InputWeightPositive = InputWeightPositive dataSet
  ; OutputWeightPositive = OutputWeightPositive dataSet
  ; inputWeightPositive = inputWeightPositive dataSet
  ; outputWeightPositive = outputWeightPositive dataSet
  ; WeightedRowSumMeaning = λ candidate →
      candidate ≡ literalWeightedRowSum dataSet
  ; WeightedColumnSumMeaning = λ candidate →
      candidate ≡ literalWeightedColumnSum dataSet
  ; weightedRowSumMeaning = refl
  ; weightedColumnSumMeaning = refl
  ; weightedRowBound = weightedRowBound dataSet
  ; weightedColumnBound = weightedColumnBound dataSet
  ; finiteWeightedSchurTest = finiteWeightedSchurTest dataSet
  }

asRelativeWeightedSchurBudget :
  ∀ {CoarseBond FineBond Scalar : Set}
    {dataSet : PeriodicPrimaryWeightedSchurInputs
      CoarseBond FineBond Scalar} →
  Weighted.RelativeWeightedSchurBudget
    (asFiniteWeightedSchurData dataSet)
asRelativeWeightedSchurBudget {dataSet = dataSet} = record
  { oneEighth = oneEighth dataSet
  ; previousNormSquared = previousNormSquared dataSet
  ; weightedProductBelowRelativeBudget =
      weightedProductBelowRelativeBudget dataSet
  }

asPrimaryQkWeightedSchurMeaning :
  ∀ {CoarseBond FineBond Scalar : Set}
    (dataSet : PeriodicPrimaryWeightedSchurInputs
      CoarseBond FineBond Scalar) →
  PrimaryWeighted.PrimaryQkWeightedSchurMeaning
    FineBond CoarseBond Scalar
asPrimaryQkWeightedSchurMeaning dataSet = record
  { additive = Periodic.algebra (primary dataSet)
  ; primaryRows = Periodic.periodicUniformPrimaryRows (primary dataSet)
  ; primaryAdjointColumns =
      Periodic.periodicUniformPrimaryAdjointColumns (primary dataSet)
  ; primalAgreement = refl
  ; weightedData = asFiniteWeightedSchurData dataSet
  ; weightedKernelIsPrimaryDerivative = refl
  ; WeightedAdjointMeaning = λ candidate →
      candidate ≡ Periodic.adjointKernelAbsoluteValue (primary dataSet)
  ; weightedAdjointMeaning = refl
  ; relativeBudget = asRelativeWeightedSchurBudget
  }

periodicPrimaryWeightedRelativeOneEighth :
  ∀ {CoarseBond FineBond Scalar : Set}
    (dataSet : PeriodicPrimaryWeightedSchurInputs
      CoarseBond FineBond Scalar) →
  Weighted.LessEqual (asFiniteWeightedSchurData dataSet)
    (Weighted.operatorNormSquared (asFiniteWeightedSchurData dataSet))
    (Weighted.multiply (asFiniteWeightedSchurData dataSet)
      (Weighted.oneEighth asRelativeWeightedSchurBudget)
      (Weighted.previousNormSquared asRelativeWeightedSchurBudget))
periodicPrimaryWeightedRelativeOneEighth dataSet =
  PrimaryWeighted.primaryQkWeightedRelativeOneEighth
    (asPrimaryQkWeightedSchurMeaning dataSet)

periodicQkLiteralWeightedRowSumLevel : ProofLevel
periodicQkLiteralWeightedRowSumLevel = computed

periodicQkLiteralWeightedColumnSumLevel : ProofLevel
periodicQkLiteralWeightedColumnSumLevel = computed

periodicQkWeightedSchurInstantiationLevel : ProofLevel
periodicQkWeightedSchurInstantiationLevel = machineChecked

periodicQkWeightedRelativeContractionAssemblyLevel : ProofLevel
periodicQkWeightedRelativeContractionAssemblyLevel = machineChecked

physicalPeriodicQkWeightChoiceInputsLevel : ProofLevel
physicalPeriodicQkWeightChoiceInputsLevel = conditional

physicalPeriodicQkWeightedBoundsInputsLevel : ProofLevel
physicalPeriodicQkWeightedBoundsInputsLevel = conditional

physicalPeriodicQkRelativeProductInputsLevel : ProofLevel
physicalPeriodicQkRelativeProductInputsLevel = conditional
