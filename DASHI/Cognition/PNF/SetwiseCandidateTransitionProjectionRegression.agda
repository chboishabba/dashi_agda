module DASHI.Cognition.PNF.SetwiseCandidateTransitionProjectionRegression where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.SetwiseCandidateTransitionProjectionExact

fiveTransitions : CandidateTransitionBatch
fiveTransitions =
  candidateTransitionBatch
    3
    2
    5
    refl
    5
    5
    refl
    refl
    4
    (s≤s (s≤s (s≤s (s≤s z≤n))))
    2
    2
    4
    refl

sameAuthorityAndCurrent : SetwiseProjectionEquivalence Nat Nat
sameAuthorityAndCurrent =
  setwiseProjectionEquivalence
    5
    5
    refl
    4
    4
    refl

concreteRuntimeBoundary : CandidateBatchRuntimeBoundary
concreteRuntimeBoundary =
  candidateBatchRuntimeBoundary fiveTransitions sameAuthorityAndCurrent
