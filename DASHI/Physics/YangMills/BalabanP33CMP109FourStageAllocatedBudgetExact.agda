module DASHI.Physics.YangMills.BalabanP33CMP109FourStageAllocatedBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Replace the single CMP109 premise
--
--   fourStageDifferenceMajorant <= rho
--
-- by four separately auditable product estimates with the exact allocation
--
--   outer       <= rho / 8,
--   logarithm   <= rho / 8,
--   transport   <= rho / 4,
--   path        <= rho / 2.
--
-- The rational identity 1/8 + 1/8 + 1/4 + 1/2 = 1 and monotonicity of finite
-- addition then construct the joint DQ_A-DQ_0 estimate.  This module also
-- constructs the existing CMP109 primitive directly, so the joint majorant is
-- no longer supplied independently of its four physical leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline
import DASHI.Physics.YangMills.BalabanP33FourStageOperatorDifferenceExact as Difference
import DASHI.Physics.YangMills.BalabanP33CMP109DerivativeDifferencePrimitiveExact as Primitive

oneEighth oneQuarter oneHalf : ℚ
oneEighth = + 1 / 8
oneQuarter = + 1 / 4
oneHalf = + 1 / 2

allocatedOuter allocatedLogarithm allocatedTransport allocatedPath : ℚ → ℚ
allocatedOuter radius = oneEighth * radius
allocatedLogarithm radius = oneEighth * radius
allocatedTransport radius = oneQuarter * radius
allocatedPath radius = oneHalf * radius

allocatedTotal : ℚ → ℚ
allocatedTotal radius =
  allocatedOuter radius
  + (allocatedLogarithm radius
    + (allocatedTransport radius + allocatedPath radius))

allocatedTotalIsRadius : ∀ radius → allocatedTotal radius ≡ radius
allocatedTotalIsRadius = ℚRing.solve-∀

fourStageMajorantAsRationalSum :
  ∀ {Operator}
    (algebra : Difference.AdditiveOperatorNormAlgebra Operator ℚ)
    (pair : Difference.FourStageBackgroundPair Operator ℚ algebra)
    (inputs : Difference.FourStageDifferenceNormInputs
      Operator ℚ algebra pair) →
  (∀ left right → Difference.addBound algebra left right ≡ left + right) →
  Difference.fourStageDifferenceMajorant inputs
  ≡ Difference.outerTermBound inputs
      + (Difference.logarithmTermBound inputs
        + (Difference.transportTermBound inputs
          + Difference.pathTermBound inputs))
fourStageMajorantAsRationalSum algebra pair inputs addMeaning =
  trans
    (addMeaning
      (Difference.outerTermBound inputs)
      (Difference.addBound algebra
        (Difference.logarithmTermBound inputs)
        (Difference.addBound algebra
          (Difference.transportTermBound inputs)
          (Difference.pathTermBound inputs))))
    (cong
      (Difference.outerTermBound inputs +_)
      (trans
        (addMeaning
          (Difference.logarithmTermBound inputs)
          (Difference.addBound algebra
            (Difference.transportTermBound inputs)
            (Difference.pathTermBound inputs)))
        (cong
          (Difference.logarithmTermBound inputs +_)
          (addMeaning
            (Difference.transportTermBound inputs)
            (Difference.pathTermBound inputs)))))

record FourStageAllocatedBudget
    {Operator : Set}
    (algebra : Difference.AdditiveOperatorNormAlgebra Operator ℚ)
    (pair : Difference.FourStageBackgroundPair Operator ℚ algebra)
    (inputs : Difference.FourStageDifferenceNormInputs
      Operator ℚ algebra pair)
    (radius : ℚ) : Set₁ where
  field
    addBoundMeaning : ∀ left right →
      Difference.addBound algebra left right ≡ left + right

    outerProductBelowAllocation :
      Difference.outerTermBound inputs ≤ allocatedOuter radius

    logarithmProductBelowAllocation :
      Difference.logarithmTermBound inputs ≤ allocatedLogarithm radius

    transportProductBelowAllocation :
      Difference.transportTermBound inputs ≤ allocatedTransport radius

    pathProductBelowAllocation :
      Difference.pathTermBound inputs ≤ allocatedPath radius

open FourStageAllocatedBudget public

fourStageAllocatedBudgetGivesRadius :
  ∀ {Operator algebra pair inputs radius}
    (budget : FourStageAllocatedBudget
      {Operator} algebra pair inputs radius) →
  Difference.fourStageDifferenceMajorant inputs ≤ radius
fourStageAllocatedBudgetGivesRadius
    {algebra = algebra} {pair = pair} {inputs = inputs} {radius = radius}
    budget =
  subst
    (λ lower → lower ≤ radius)
    (sym
      (fourStageMajorantAsRationalSum
        algebra pair inputs (addBoundMeaning budget)))
    (subst
      (λ upper →
        Difference.outerTermBound inputs
        + (Difference.logarithmTermBound inputs
          + (Difference.transportTermBound inputs
            + Difference.pathTermBound inputs))
        ≤ upper)
      (allocatedTotalIsRadius radius)
      (ℚP.+-mono-≤
        (outerProductBelowAllocation budget)
        (ℚP.+-mono-≤
          (logarithmProductBelowAllocation budget)
          (ℚP.+-mono-≤
            (transportProductBelowAllocation budget)
            (pathProductBelowAllocation budget)))))

asCMP109DerivativeDifferencePrimitive :
  ∀ {Operator Cell}
    (algebra : Difference.AdditiveOperatorNormAlgebra Operator ℚ)
    (pair : Difference.FourStageBackgroundPair Operator ℚ algebra)
    (inputs : Difference.FourStageDifferenceNormInputs
      Operator ℚ algebra pair)
    (radius : ℚ) →
  Pipeline.LessEqual (Difference.normAlgebra algebra) ≡ _≤_ →
  (coordinate : Operator → Cell → ℚ) →
  (∀ operator cell →
    ∣ coordinate operator cell ∣
    ≤ Pipeline.operatorNorm (Difference.normAlgebra algebra) operator) →
  FourStageAllocatedBudget algebra pair inputs radius →
  Primitive.CMP109DerivativeDifferencePrimitive Operator Cell
asCMP109DerivativeDifferencePrimitive
    algebra pair inputs radius orderMeaning coordinate coordinateBound budget =
  record
    { Primitive.CMP109DerivativeDifferencePrimitive.algebra = algebra
    ; Primitive.CMP109DerivativeDifferencePrimitive.pair = pair
    ; Primitive.CMP109DerivativeDifferencePrimitive.normInputs = inputs
    ; Primitive.CMP109DerivativeDifferencePrimitive.radius = radius
    ; Primitive.CMP109DerivativeDifferencePrimitive.orderMeaning = orderMeaning
    ; Primitive.CMP109DerivativeDifferencePrimitive.majorantBelowRadius =
        fourStageAllocatedBudgetGivesRadius budget
    ; Primitive.CMP109DerivativeDifferencePrimitive.coordinate = coordinate
    ; Primitive.CMP109DerivativeDifferencePrimitive.coordinateBelowOperatorNorm =
        coordinateBound
    }

cmp109FourStageAllocationArithmeticLevel : ProofLevel
cmp109FourStageAllocationArithmeticLevel = machineChecked

cmp109FourStageAllocatedMajorantLevel : ProofLevel
cmp109FourStageAllocatedMajorantLevel = machineChecked

cmp109AllocatedPrimitiveConstructionLevel : ProofLevel
cmp109AllocatedPrimitiveConstructionLevel = machineChecked
