module DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanCompensatedTAdapterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; _≤_)
open import Data.Rational.Properties using (*-comm)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Factors
import DASHI.Physics.YangMills.BalabanClayGate4TCompensatedSixFactorBudgetExact as Compensated
import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanDeterminantLossExact as Determinant

------------------------------------------------------------------------
-- This adapter supplies the determinantCompensated field consumed by the
-- compensated six-factor T-operation budget. The finite determinant theorem is
-- already assembled; the remaining input is the physical identification of the
-- Hessian matrices, determinant factors and rational order.
------------------------------------------------------------------------

record IpsenRehmanCompensatedTMeaning
    {Scale Traversal Matrix : Set}
    (comparison : Compensated.CompensatedSixFactorComparison Scale Traversal)
    (meaning : Determinant.PhysicalRelativeHessianDeterminantMeaning
      Scale Traversal Matrix ℚ) : Set₁ where
  field
    determinantOrderMeaning : ∀ scale traversal {left right} →
      Determinant.LessEqual
        (Determinant.determinantData meaning scale traversal)
        left right →
      left ≤ right

    multiplyMeaning : ∀ scale traversal left right →
      Determinant.multiply
        (Determinant.determinantData meaning scale traversal)
        left right
      ≡ left * right

    physicalFactorMeaning : ∀ scale traversal →
      Factors.determinantFactor
        (Compensated.physical comparison) scale traversal
      ≡ Determinant.physicalDeterminant meaning scale traversal

    referenceFactorMeaning : ∀ scale traversal →
      Compensated.referenceDeterminant comparison scale traversal
      ≡ Determinant.referenceDeterminant meaning scale traversal

    multiplierMeaning : ∀ scale traversal →
      Compensated.determinantLoss comparison scale traversal
      ≡ Determinant.determinantMultiplier meaning scale traversal

open IpsenRehmanCompensatedTMeaning public

ipsenRehmanSuppliesDeterminantCompensated :
  ∀ {Scale Traversal Matrix}
    {comparison : Compensated.CompensatedSixFactorComparison Scale Traversal}
    {meaning : Determinant.PhysicalRelativeHessianDeterminantMeaning
      Scale Traversal Matrix ℚ} →
  IpsenRehmanCompensatedTMeaning comparison meaning →
  ∀ scale traversal →
  Factors.determinantFactor
    (Compensated.physical comparison) scale traversal
  ≤ Compensated.determinantLoss comparison scale traversal
      * Compensated.referenceDeterminant comparison scale traversal
ipsenRehmanSuppliesDeterminantCompensated
  {comparison = comparison} {meaning = meaning} bridge scale traversal =
  let dataSet = Determinant.determinantData meaning scale traversal
      physicalValue = Determinant.physicalDeterminant meaning scale traversal
      referenceValue = Determinant.referenceDeterminant meaning scale traversal
      multiplierValue = Determinant.determinantMultiplier meaning scale traversal
      base = determinantOrderMeaning bridge scale traversal
        (Determinant.physicalDeterminantBelowIpsenRehmanMultiplier
          meaning scale traversal)
      commute : referenceValue * multiplierValue ≡ multiplierValue * referenceValue
      commute = *-comm referenceValue multiplierValue
      comparisonProductMeaning :
        Compensated.determinantLoss comparison scale traversal
          * Compensated.referenceDeterminant comparison scale traversal
        ≡ multiplierValue * referenceValue
      comparisonProductMeaning = cong₂ _*_
        (multiplierMeaning bridge scale traversal)
        (referenceFactorMeaning bridge scale traversal)
      upperMeaning :
        referenceValue * multiplierValue
        ≡ Compensated.determinantLoss comparison scale traversal
            * Compensated.referenceDeterminant comparison scale traversal
      upperMeaning = trans commute (sym comparisonProductMeaning)
  in subst
      (λ upper → Factors.determinantFactor
        (Compensated.physical comparison) scale traversal ≤ upper)
      upperMeaning
      (subst
        (λ lower → lower ≤ referenceValue * multiplierValue)
        (sym (physicalFactorMeaning bridge scale traversal))
        (subst
          (λ mult → physicalValue ≤ mult)
          (multiplyMeaning bridge scale traversal referenceValue multiplierValue)
          base))

ipsenRehmanCompensatedTAdapterLevel : ProofLevel
ipsenRehmanCompensatedTAdapterLevel = machineChecked

physicalFiniteHessianToTDeterminantMeaningInputsLevel : ProofLevel
physicalFiniteHessianToTDeterminantMeaningInputsLevel = conditional

physicalDeterminantRationalOrderMeaningInputsLevel : ProofLevel
physicalDeterminantRationalOrderMeaningInputsLevel = conditional
