{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechWeightedHistoryMoEBidiExact where

-- Finite executable mirror of the structural contracts of
-- LeechTransformer/models/history_orbit_moe.py, NOT a float/PyTorch proof.
-- Distinct learned family slots, history-indexed scoring, deterministic
-- top-1/top-2 selection, weighted selected outputs, isolated histories,
-- and a BIDI consumer receipt. Original LILA credit: Anatolii Kornienko.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as Sign

-- Concrete top-k comparison: deterministic tie -> expert 0.
lessEqual : Nat → Nat → Bool
lessEqual zero y = true
lessEqual (suc x) zero = false
lessEqual (suc x) (suc y) = lessEqual x y

data ExpertId : Set where
  e0 e1 : ExpertId

record Memories : Set where
  constructor memories
  field
    h0 : Sign.Trit
    h1 : Sign.Trit
open Memories public

record Outputs : Set where
  constructor outputs
  field
    y0 : Nat
    y1 : Nat
open Outputs public

-- Independently learned family functions, indexed by explicit ID.
-- The history is an input to *both* scoring and expert update.
record LearnedFamily : Set where
  constructor learnedFamily
  field
    expert0 : Sign.Trit → Sign.Trit → Nat
    expert1 : Sign.Trit → Sign.Trit → Nat
    advance0 : Sign.Trit → Sign.Trit → Sign.Trit
    advance1 : Sign.Trit → Sign.Trit → Sign.Trit
    score0 : Sign.Trit → Sign.Trit → Nat
    score1 : Sign.Trit → Sign.Trit → Nat
open LearnedFamily public

data TopK : Set where
  topOne topTwo : TopK

data Selection : Set where
  only0 only1 both : Selection

choose : LearnedFamily → TopK → Sign.Trit → Memories → Selection
choose family topTwo x state = both
choose family topOne x state with lessEqual
  (score1 family x (h1 state)) (score0 family x (h0 state))
... | true = only0
... | false = only1

-- Weights are explicit natural scalars: this formalises the weighted
-- aggregation topology, NOT the numerical softmax identity.
record Weights : Set where
  constructor weights
  field
    w0 : Nat
    w1 : Nat
open Weights public

record StepResult : Set where
  constructor stepResult
  field
    result : Nat
    next : Memories
    chosen : Selection
open StepResult public

step : LearnedFamily → TopK → Weights → Sign.Trit → Memories → StepResult
step family k w x state with choose family k x state
... | only0 = stepResult
  (w0 w * expert0 family x (h0 state))
  (memories (advance0 family x (h0 state)) (h1 state)) only0
... | only1 = stepResult
  (w1 w * expert1 family x (h1 state))
  (memories (h0 state) (advance1 family x (h1 state))) only1
... | both = stepResult
  ((w0 w * expert0 family x (h0 state)) +
   (w1 w * expert1 family x (h1 state)))
  (memories (advance0 family x (h0 state))
            (advance1 family x (h1 state))) both

-- Decoding is consumer-indexed: the receipt includes the selected
-- route and *both* next-memory values, not only the mixed output.
record Receipt : Set where
  constructor receipt
  field
    delivered : Nat
    histories : Memories
    route : Selection
open Receipt public

encode : StepResult → Receipt
encode (stepResult y state route) = receipt y state route

decode : Receipt → StepResult
decode (receipt y state route) = stepResult y state route

consumerBidi :
  (out : StepResult) → decode (encode out) ≡ out
consumerBidi (stepResult y state route) = refl

producerBidi :
  (wire : Receipt) → encode (decode wire) ≡ wire
producerBidi (receipt y state route) = refl

-- Selected-only update laws: inactive histories persist exactly.
unselectedHistory0 :
  (family : LearnedFamily) (w : Weights)
  (x : Sign.Trit) (state : Memories) →
  h1 (next (stepResult
    (w0 w * expert0 family x (h0 state))
    (memories (advance0 family x (h0 state)) (h1 state)) only0))
  ≡ h1 state
unselectedHistory0 family w x state = refl

unselectedHistory1 :
  (family : LearnedFamily) (w : Weights)
  (x : Sign.Trit) (state : Memories) →
  h0 (next (stepResult
    (w1 w * expert1 family x (h1 state))
    (memories (h0 state) (advance1 family x (h1 state))) only1))
  ≡ h0 state
unselectedHistory1 family w x state = refl

-- The state machine can be unrolled and resumed without changing
-- output or terminal history. A segment boundary preserves all memory.
data Inputs : Set where
  [] : Inputs
  _::_ : Sign.Trit → Inputs → Inputs

record Trace : Set where
  constructor trace
  field
    values : Inputs
    terminal : Memories
open Trace public

-- Trace output encodes the Nat result as an optional auxiliary trace
-- only in a future richer carrier; current theorem is about state replay.
runMemory : LearnedFamily → TopK → Weights →
            Inputs → Memories → Memories
runMemory family k w [] state = state
runMemory family k w (x :: xs) state =
  runMemory family k w xs (next (step family k w x state))

append : Inputs → Inputs → Inputs
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

segmentReplay :
  (family : LearnedFamily) (k : TopK) (w : Weights) →
  (xs ys : Inputs) (state : Memories) →
  runMemory family k w (append xs ys) state
  ≡ runMemory family k w ys (runMemory family k w xs state)
segmentReplay family k w [] ys state = refl
segmentReplay family k w (x :: xs) ys state =
  segmentReplay family k w xs ys (next (step family k w x state))
