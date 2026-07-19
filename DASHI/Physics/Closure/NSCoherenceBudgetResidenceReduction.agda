module DASHI.Physics.Closure.NSCoherenceBudgetResidenceReduction where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set)
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- Algebraic kernel of the coherence-budget residence strategy.
--
-- The PDE-facing work must construct:
--
--   margin * localDepletion <= budgetUpper
--   dangerCost * dangerousResidence <= localDepletion.
--
-- The first inequality is where the integrated pressure-Hessian,
-- cross-shell-commutator, and cutoff remainders must be absorbed. The second
-- is where dangerous Gamma is shown to spend local depletion. This module
-- proves the exact composition used by the residence argument.
------------------------------------------------------------------------

record OrderedBudgetArithmetic : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    _*_ : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

    ≤-trans :
      {a b c : Scalar} → _≤_ a b → _≤_ b c → _≤_ a c

    multiplicationAssociative :
      (a b c : Scalar) → _*_ (_*_ a b) c ≡ _*_ a (_*_ b c)

    multiplicationMonotoneNonnegativeLeft :
      {a b c : Scalar} →
      _≤_ zero a →
      _≤_ b c →
      _≤_ (_*_ a b) (_*_ a c)

    multiplicationZeroLeft :
      (a : Scalar) → _*_ zero a ≡ zero

    multiplicationZeroRight :
      (a : Scalar) → _*_ a zero ≡ zero

open OrderedBudgetArithmetic public

record CoherenceBudgetResidenceInputs
    (A : OrderedBudgetArithmetic) : Set₁ where
  field
    absorptionMargin : Scalar A
    dangerCost : Scalar A
    dangerousResidence : Scalar A
    localDepletion : Scalar A
    budgetUpper : Scalar A

    absorptionMarginNonnegative :
      _≤_ A (zero A) absorptionMargin

    dangerousTransferConsumesDepletion :
      _≤_ A
        (_*_ A dangerCost dangerousResidence)
        localDepletion

    pressureRemainderAbsorbedIntoBudget :
      _≤_ A
        (_*_ A absorptionMargin localDepletion)
        budgetUpper

open CoherenceBudgetResidenceInputs public

coherenceBudgetForcesResidenceBound :
  (A : OrderedBudgetArithmetic) →
  (I : CoherenceBudgetResidenceInputs A) →
  _≤_ A
    (_*_ A
      (_*_ A (absorptionMargin I) (dangerCost I))
      (dangerousResidence I))
    (budgetUpper I)
coherenceBudgetForcesResidenceBound A I =
  subst
    (λ lhs → _≤_ A lhs (budgetUpper I))
    (sym (multiplicationAssociative A
      (absorptionMargin I)
      (dangerCost I)
      (dangerousResidence I)))
    (≤-trans A
      (multiplicationMonotoneNonnegativeLeft A
        (absorptionMarginNonnegative I)
        (dangerousTransferConsumesDepletion I))
      (pressureRemainderAbsorbedIntoBudget I))

------------------------------------------------------------------------
-- Quasi-2D stability specialization. A proved stability inequality turns
-- exact rank-two/columnar defect zero into pressure-mix vanishing.
------------------------------------------------------------------------

record Quasi2DPressureHessianStabilityInputs
    (A : OrderedBudgetArithmetic) : Set₁ where
  field
    pressureMixAbsolute : Scalar A
    stabilityConstant : Scalar A
    planarityDefect : Scalar A
    normFactor : Scalar A

    stabilityEstimate :
      _≤_ A pressureMixAbsolute
        (_*_ A stabilityConstant (_*_ A planarityDefect normFactor))

open Quasi2DPressureHessianStabilityInputs public

exactColumnarPressureMixIsBoundedByZero :
  (A : OrderedBudgetArithmetic) →
  (I : Quasi2DPressureHessianStabilityInputs A) →
  planarityDefect I ≡ zero A →
  _≤_ A (pressureMixAbsolute I) (zero A)
exactColumnarPressureMixIsBoundedByZero A I defectZero =
  subst
    (λ rhs → _≤_ A (pressureMixAbsolute I) rhs)
    rhsIsZero
    (stabilityEstimate I)
  where
  rhsIsZero :
    _*_ A (stabilityConstant I) (_*_ A (planarityDefect I) (normFactor I))
      ≡ zero A
  rhsIsZero =
    let
      innerIsZero :
        _*_ A (planarityDefect I) (normFactor I) ≡ zero A
      innerIsZero =
        subst
          (λ d → _*_ A d (normFactor I) ≡ zero A)
          (sym defectZero)
          (multiplicationZeroLeft A (normFactor I))
    in
    subst
      (λ inner → _*_ A (stabilityConstant I) inner ≡ zero A)
      (sym innerIsZero)
      (multiplicationZeroRight A (stabilityConstant I))
