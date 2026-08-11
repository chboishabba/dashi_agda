module DASHI.Cognition.PNF.BoundedFactorCompositionExecution where

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Migrations 082 and 084 execution contract.
--
-- Retained composition candidates are bounded before materialisation, and the
-- raw-pair LIMIT is applied before candidate ranking. If the structural pair
-- carrier is larger than the retained budget, runtime records an overflow
-- receipt. Overflow is execution evidence only; it cannot itself reject a
-- semantic relation or license a derived proposition.
------------------------------------------------------------------------

record CompositionEnumeration : Set where
  constructor compositionEnumeration
  field
    possiblePairCount : Nat
    retainedPairCount : Nat
    retainedPairLimit : Nat
    retainedWithinLimit : retainedPairCount ≤ᶜ retainedPairLimit

open CompositionEnumeration public

data CompositionOverflowState : Set where
  completeWithinBudget overflowObserved : CompositionOverflowState

record CompositionOverflowReceipt : Set where
  constructor compositionOverflowReceipt
  field
    enumeration : CompositionEnumeration
    overflowState : CompositionOverflowState

open CompositionOverflowReceipt public

data OverflowSemanticAuthority : Set where
  executionEvidenceOnly : OverflowSemanticAuthority

-- No constructor exists. An overflow receipt therefore cannot be promoted into
-- semantic composition authority merely because some structural pairs were not
-- retained in the bounded execution frontier.
data OverflowCompositionPermission : OverflowSemanticAuthority → Set where

executionOverflowCannotCompose :
  OverflowCompositionPermission executionEvidenceOnly → ⊥
executionOverflowCannotCompose ()

record BoundedCompositionExecutionBoundary : Set where
  constructor boundedCompositionExecutionBoundary
  field
    overflowAuthority : OverflowSemanticAuthority
    overflowHasNoSemanticPermission :
      OverflowCompositionPermission executionEvidenceOnly → ⊥

open BoundedCompositionExecutionBoundary public

canonicalBoundedCompositionExecutionBoundary : BoundedCompositionExecutionBoundary
canonicalBoundedCompositionExecutionBoundary =
  boundedCompositionExecutionBoundary
    executionEvidenceOnly
    executionOverflowCannotCompose
