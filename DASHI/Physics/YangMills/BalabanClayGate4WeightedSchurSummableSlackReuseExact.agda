module DASHI.Physics.YangMills.BalabanClayGate4WeightedSchurSummableSlackReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurBlockAdjointExact as Weighted
import DASHI.Physics.YangMills.BalabanClayGate4NearContractionSummableSlackExact as Slack

------------------------------------------------------------------------
-- Weighted Schur to near-contraction adapter.
--
-- The exact weighted theorem gives
--
--   operatorNormSquared_k <= alpha_k beta_k.
--
-- A physical relative budget may take either the exact form
--
--   alpha_k beta_k <= (1/8) S_k
--
-- or the corrected form
--
--   alpha_k beta_k <= (1/8 + delta_k) S_k.
--
-- This module transports either form into the common near-contraction
-- recursion.  The sibling summable-slack theorem then controls the product of
-- the correction factors.  No numerical delta sequence is invented here.
------------------------------------------------------------------------

record WeightedSchurNearContractionInputs
    (Input Output Scalar : Set) : Set₁ where
  field
    algebra : Slack.OrderedExponentialProduct Scalar
    weightedData : Nat → Weighted.FiniteWeightedSchurData Input Output Scalar

    state factor : Nat → Scalar

    operatorNormStateMeaning : ∀ count →
      state (suc count)
      ≡ Weighted.operatorNormSquared (weightedData count)

    weightedOrderToNearOrder : ∀ count {left right} →
      Weighted.LessEqual (weightedData count) left right →
      Slack.LessEqual algebra left right

    weightedMultiplyMeaning : ∀ count left right →
      Weighted.multiply (weightedData count) left right
      ≡ Slack.multiply algebra left right

    weightedProductBelowNearFactor : ∀ count →
      Weighted.LessEqual (weightedData count)
        (Weighted.multiply (weightedData count)
          (Weighted.alpha (weightedData count))
          (Weighted.beta (weightedData count)))
        (Weighted.multiply (weightedData count)
          (factor count) (state count))

open WeightedSchurNearContractionInputs public

weightedSchurNearStep :
  ∀ {Input Output Scalar}
    (inputs : WeightedSchurNearContractionInputs Input Output Scalar)
    count →
  Slack.LessEqual (algebra inputs)
    (state inputs (suc count))
    (Slack.multiply (algebra inputs)
      (factor inputs count) (state inputs count))
weightedSchurNearStep inputs count =
  subst
    (λ lower → Slack.LessEqual (algebra inputs) lower
      (Slack.multiply (algebra inputs)
        (factor inputs count) (state inputs count)))
    (sym (operatorNormStateMeaning inputs count))
    (subst
      (λ upper → Slack.LessEqual (algebra inputs)
        (Weighted.operatorNormSquared (weightedData inputs count)) upper)
      (weightedMultiplyMeaning inputs count
        (factor inputs count) (state inputs count))
      (Slack.transitive (algebra inputs)
        (weightedOrderToNearOrder inputs count
          (Weighted.finiteWeightedSchurTest (weightedData inputs count)))
        (weightedOrderToNearOrder inputs count
          (weightedProductBelowNearFactor inputs count))))

asNearContractionRecursion :
  ∀ {Input Output Scalar}
    (inputs : WeightedSchurNearContractionInputs Input Output Scalar) →
  Slack.NearContractionRecursion Scalar
asNearContractionRecursion inputs = record
  { algebra = algebra inputs
  ; state = state inputs
  ; factor = factor inputs
  ; stepBound = weightedSchurNearStep inputs
  }

record PhysicalWeightedSchurSlackFactorization
    {Input Output Scalar : Set}
    (inputs : WeightedSchurNearContractionInputs Input Output Scalar) : Set₁ where
  field
    factorization : Slack.SummableSlackFactorization
      (asNearContractionRecursion inputs)

    PhysicalStateMeaning : (Nat → Scalar) → Set
    PhysicalFactorMeaning : (Nat → Scalar) → Set

    physicalStateMeaning : PhysicalStateMeaning (state inputs)
    physicalFactorMeaning : PhysicalFactorMeaning (factor inputs)

open PhysicalWeightedSchurSlackFactorization public

physicalWeightedSchurStateEnvelope :
  ∀ {Input Output Scalar}
    {inputs : WeightedSchurNearContractionInputs Input Output Scalar}
    (meaning : PhysicalWeightedSchurSlackFactorization inputs)
    count →
  Slack.LessEqual (algebra inputs)
    (state inputs count)
    (Slack.multiply (algebra inputs)
      (Slack.multiply (algebra inputs)
        (Slack.rhoPower (factorization meaning) count)
        (Slack.exponential (algebra inputs)
          (Slack.totalSlack (factorization meaning))))
      (state inputs Nat.zero))
physicalWeightedSchurStateEnvelope meaning count =
  Slack.stateBelowSummableSlackEnvelope
    (factorization meaning) count

weightedSchurNearContractionAdapterLevel : ProofLevel
weightedSchurNearContractionAdapterLevel = machineChecked

weightedSchurSummableSlackEnvelopeLevel : ProofLevel
weightedSchurSummableSlackEnvelopeLevel = machineChecked

physicalWeightedSchurStateMeaningInputsLevel : ProofLevel
physicalWeightedSchurStateMeaningInputsLevel = conditional

physicalWeightedSchurNearFactorBudgetInputsLevel : ProofLevel
physicalWeightedSchurNearFactorBudgetInputsLevel = conditional

physicalWeightedSchurSlackSummabilityInputsLevel : ProofLevel
physicalWeightedSchurSlackSummabilityInputsLevel = conditional
