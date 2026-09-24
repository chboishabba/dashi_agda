module DASHI.Mathematics.Complexity.PNotEqualsNPTransitionAlgebraicAuthorityExact where

------------------------------------------------------------------------
-- ALGEBRAIC TRANSITION LAW -> GLOBAL ITERATE AUTHORITY
--
-- Positive control for the surviving P11 programme.
--
-- If a deterministic transition F satisfies the global algebraic law
--
--   F (F x) = x
--
-- for every state, then an exponentially long family of concrete executions
-- collapses semantically:
--
--   F^(2^d) x = x       for every d >= 1.
--
-- No intermediate trajectory is represented or checked.  The reusable
-- authority is the algebraic involution theorem itself.
--
-- This is NOT asserted for SAT computation.  It demonstrates precisely what
-- kind of theorem can beat trajectory/circuit size honestly: an independently
-- proved semantic law on the transition operator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- Iteration.
------------------------------------------------------------------------

iterate :
  ∀ {State : Set} →
  Nat →
  (State → State) →
  State →
  State
iterate zero step state =
  state
iterate (suc count) step state =
  iterate count step (step state)

iterateAdd :
  ∀ {State : Set}
    (left right : Nat)
    (step : State → State)
    (state : State) →
  iterate (left + right) step state
  ≡
  iterate right step
    (iterate left step state)
iterateAdd zero right step state =
  refl
iterateAdd (suc left) right step state =
  iterateAdd left right step (step state)

------------------------------------------------------------------------
-- Powers of two.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero =
  suc zero
pow2 (suc exponent) =
  pow2 exponent + pow2 exponent

------------------------------------------------------------------------
-- Algebraic authority.
------------------------------------------------------------------------

Involutive :
  ∀ {State : Set} →
  (State → State) →
  Set
Involutive step =
  (state : _) →
  step (step state) ≡ state

iterateTwoIsIdentity :
  ∀ {State : Set}
    (step : State → State) →
  Involutive step →
  (state : State) →
  iterate (suc (suc zero)) step state
  ≡ state
iterateTwoIsIdentity step involutive state =
  involutive state

------------------------------------------------------------------------
-- Once one power-of-two iterate is identity, doubling the exponent preserves
-- identity by iterateAdd.  The base case d=1 is the involution law itself.
------------------------------------------------------------------------

powerOfTwoIterateIdentity :
  ∀ {State : Set}
    (step : State → State) →
  Involutive step →
  (depth : Nat) →
  (state : State) →
  iterate
    (pow2 (suc depth))
    step
    state
  ≡ state
powerOfTwoIterateIdentity
    step involutive zero state =
  involutive state
powerOfTwoIterateIdentity
    step involutive (suc depth) state =
  trans
    (iterateAdd
      (pow2 (suc depth))
      (pow2 (suc depth))
      step
      state)
    (trans
      (cong
        (iterate (pow2 (suc depth)) step)
        (powerOfTwoIterateIdentity
          step involutive depth state))
      (powerOfTwoIterateIdentity
        step involutive depth state))

------------------------------------------------------------------------
-- A reusable authority object contains ONLY the algebraic law, not a supplied
-- result for each horizon.
------------------------------------------------------------------------

record InvolutionAuthority
    (State : Set)
    (step : State → State) : Set₁ where
  constructor involution-authority
  field
    involutionLaw :
      Involutive step

open InvolutionAuthority public

authorityClosesEveryPowerOfTwoExecution :
  ∀ {State : Set}
    {step : State → State} →
  InvolutionAuthority State step →
  (depth : Nat) →
  (state : State) →
  iterate
    (pow2 (suc depth))
    step
    state
  ≡ state
authorityClosesEveryPowerOfTwoExecution
    authority depth state =
  powerOfTwoIterateIdentity
    _
    (involutionLaw authority)
    depth
    state

------------------------------------------------------------------------
-- Research consequence.
--
-- P11's surviving positive target should have this shape:
--
--   fixed uniform program/self-evaluation operator
--           +
--   independently derived algebraic/semantic law
--           =>
--   many-step evaluation theorem with tiny per-instance evidence.
--
-- Uniformity alone does not supply such a law (the full-trace-cube no-go
-- proves that).  The open question is whether SAT self-instantiation forces a
-- comparably strong law which is not itself equivalent to knowing the answer.
------------------------------------------------------------------------
