{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechFullOutputHistoryTraceBidiExact where

-- Full causal TRACE replay, consuming existing two-expert finite step.
-- Unlike memory-only segmentReplay, output, route and next memories
-- are retained for every token. No Python/float simulation is asserted.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Reasoning.LeechWeightedHistoryMoEBidiExact as M
open M using (Inputs; []; _::_; append)
import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as S

record Event : Set where
  constructor event
  field
    output : Nat
    route : M.Selection
    after : M.Memories
open Event public

record Trace : Set where
  constructor trace
  field
    events : List Event
    final : M.Memories
open Trace public

prepend : Event → Trace → Trace
prepend e (trace es h) = trace (e ∷ es) h

makeEvent : M.StepResult → Event
makeEvent s = event (M.result s) (M.chosen s) (M.next s)

-- Continuation parameter makes the exact source of sequence splitting
-- explicit and avoids assuming commutativity of weighted history steps.
runK : M.LearnedFamily → M.TopK → M.Weights →
       M.Inputs → M.Memories → (M.Memories → Trace) → Trace
runK family k w [] h continuation = continuation h
runK family k w (x :: xs) h continuation =
  prepend (makeEvent step)
    (runK family k w xs (M.next step) continuation)
  where
    step : M.StepResult
    step = M.step family k w x h

finish : M.Memories → Trace
finish h = trace (Agda.Builtin.List.[]) h

run : M.LearnedFamily → M.TopK → M.Weights →
      M.Inputs → M.Memories → Trace
run family k w xs h = runK family k w xs h finish

-- BIDI: for arbitrary future consumers of the final memory, a split
-- execution and one uninterrupted execution produce exactly the same
-- full event stream including each output, selected route and history.
splitFullTrace :
  (family : M.LearnedFamily) (k : M.TopK) (w : M.Weights) →
  (xs ys : M.Inputs) (h : M.Memories)
  (continuation : M.Memories → Trace) →
  runK family k w (M.append xs ys) h continuation
  ≡ runK family k w xs h
      (λ afterPrefix → runK family k w ys afterPrefix continuation)
splitFullTrace family k w [] ys h continuation = refl
splitFullTrace family k w (x :: xs) ys h continuation
  rewrite splitFullTrace family k w xs ys
    (M.next (M.step family k w x h)) continuation = refl

-- The transport *event* is an independently reconstructible finite
-- receipt; real floating-point model parameters and packet security
-- require distinct downstream proof obligations.
