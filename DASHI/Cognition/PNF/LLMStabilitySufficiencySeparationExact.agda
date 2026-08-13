module DASHI.Cognition.PNF.LLMStabilitySufficiencySeparationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Metric stability and semantic/future sufficiency are independent proof
-- obligations.  This finite theorem mirrors the architectural separation
-- between non-expansive residual transport (e.g. mHC-style constraints) and
-- attention/KV compression sufficiency; it does not formalize mHC numerics.
------------------------------------------------------------------------

data TwoState : Set where
  leftState rightState : TwoState

fineDistance : TwoState → TwoState → Nat
fineDistance leftState leftState = 0
fineDistance rightState rightState = 0
fineDistance leftState rightState = 1
fineDistance rightState leftState = 1

boolDistance : Bool → Bool → Nat
boolDistance false false = 0
boolDistance true true = 0
boolDistance false true = 1
boolDistance true false = 1

consumerObservation : TwoState → Bool
consumerObservation leftState = false
consumerObservation rightState = true

stableButLossy : TwoState → Bool
stableButLossy state = false

stableButLossyIsNonExpansive :
  (x y : TwoState) →
  boolDistance (stableButLossy x) (stableButLossy y)
  ≤ fineDistance x y
stableButLossyIsNonExpansive leftState leftState = z≤n
stableButLossyIsNonExpansive leftState rightState = z≤n
stableButLossyIsNonExpansive rightState leftState = z≤n
stableButLossyIsNonExpansive rightState rightState = z≤n

stableMapCannotCarryConsumerObservation :
  (decode : Bool → Bool) →
  ((state : TwoState) →
    consumerObservation state ≡ decode (stableButLossy state)) →
  ⊥
stableMapCannotCarryConsumerObservation decode factors =
  contradiction
    (trans (factors leftState) (sym (factors rightState)))
  where
    contradiction : false ≡ true → ⊥
    contradiction ()

------------------------------------------------------------------------
-- Conversely, an exact sufficient representation need not strictly contract.
------------------------------------------------------------------------

exactRepresentation : TwoState → TwoState
exactRepresentation state = state

exactRepresentationIsSufficient :
  (state : TwoState) →
  consumerObservation (exactRepresentation state)
  ≡ consumerObservation state
exactRepresentationIsSufficient state = refl

exactRepresentationPreservesNonzeroDistance :
  fineDistance (exactRepresentation leftState) (exactRepresentation rightState)
  ≡ 1
exactRepresentationPreservesNonzeroDistance = refl

exactRepresentationIsNotZeroContractingAtDistinctPair :
  fineDistance (exactRepresentation leftState) (exactRepresentation rightState)
  ≡ 0 → ⊥
exactRepresentationIsNotZeroContractingAtDistinctPair ()

------------------------------------------------------------------------
-- Therefore:
--   non-expansive/stable does not imply consumer sufficiency;
--   consumer sufficiency does not imply strict contraction.
------------------------------------------------------------------------
