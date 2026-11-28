module DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact where

------------------------------------------------------------------------
-- Input-indexed future-consumer theorem for the original recurrent
-- HistoryOrbitMoE interface, formulated as deterministic state semantics.
--
-- Unlike the existing autonomous futureConsumerSufficiency theorem,
-- this one quantifies over ALL finite future input words. The result is
-- parametric: the original learned Torch step still needs a separately
-- owned source/precision interpretation to instantiate this carrier.
--
-- Attribution: original Leech-LILA by Anatolii Kornienko.
-- Reuses the earlier consumer-fibre principle; no claim of fitted
-- source authentication, neural semantic identity or kernel execution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

cong : ∀ {A B : Set}{x y : A} (f : A → B) →
       x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set}{a a' : A}{b b' : B} →
        (f : A → B → C) → a ≡ a' → b ≡ b' →
        f a b ≡ f a' b'
cong₂ f refl refl = refl

consHead : ∀ {A : Set}{x y : A}{xs ys : List A} →
           (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
consHead refl = refl

consTail : ∀ {A : Set}{x y : A}{xs ys : List A} →
           (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
consTail refl = refl

-- Outputs are measured BEFORE the corresponding source transition.
-- The input carrier may encode intervention settings as well as x.
trace : ∀ {Input State Output : Set} →
        (Input → State → State) →
        (Input → State → Output) →
        List Input → State → List Output
trace step observe [] state = []
trace step observe (u ∷ rest) state =
  observe u state ∷ trace step observe rest (step u state)

TraceEquivalent :
  ∀ {Input State Output : Set} →
  (Input → State → State) →
  (Input → State → Output) →
  State → State → Set
TraceEquivalent {Input} step observe a b =
  (inputs : List Input) →
  trace step observe inputs a ≡ trace step observe inputs b

-- A code whose fibres preserve every original one-step output and
-- remain stable under every permitted input has matching future traces.
-- The proof never assumes that the compressed code is injective.
inputIndexedTraceDescent :
  ∀ {Input State Output Code : Set} →
  (step : Input → State → State) →
  (observe : Input → State → Output) →
  (encode : State → Code) →
  ((u : Input) (x y : State) →
    encode x ≡ encode y → observe u x ≡ observe u y) →
  ((u : Input) (x y : State) →
    encode x ≡ encode y →
    encode (step u x) ≡ encode (step u y)) →
  (inputs : List Input) (x y : State) →
  encode x ≡ encode y →
  trace step observe inputs x ≡ trace step observe inputs y
inputIndexedTraceDescent step observe encode outputStable
  transitionStable [] x y same = refl
inputIndexedTraceDescent step observe encode outputStable
  transitionStable (u ∷ rest) x y same =
  cong₂ _∷_
    (outputStable u x y same)
    (inputIndexedTraceDescent step observe encode outputStable
      transitionStable rest (step u x) (step u y)
      (transitionStable u x y same))

-- Equivalent traces have identical current outputs at EVERY input.
traceEquivalentObserves :
  ∀ {Input State Output : Set} →
  (step : Input → State → State) →
  (observe : Input → State → Output) →
  (x y : State) →
  TraceEquivalent step observe x y →
  (u : Input) → observe u x ≡ observe u y
traceEquivalentObserves step observe x y equivalent u =
  consHead (equivalent (u ∷ []))

-- And their successor states are again trace equivalent for EVERY
-- input. The shift is proven by removing the leading output.
traceEquivalentTransitions :
  ∀ {Input State Output : Set} →
  (step : Input → State → State) →
  (observe : Input → State → Output) →
  (x y : State) →
  TraceEquivalent step observe x y →
  (u : Input) →
  TraceEquivalent step observe (step u x) (step u y)
traceEquivalentTransitions step observe x y equivalent u rest =
  consTail (equivalent (u ∷ rest))

-- Thus full future-trace equivalence is the coarsest possible
-- observer-compatible, transition-stable STATE IDENTIFICATION:
-- every sufficient encoder's fibre is contained in it.
-- This is NOT an optimality claim for finite bits or arbitrary encoders.
everyStableCodecFibreIsTraceEquivalent :
  ∀ {Input State Output Code : Set} →
  (step : Input → State → State) →
  (observe : Input → State → Output) →
  (encode : State → Code) →
  ((u : Input) (x y : State) →
    encode x ≡ encode y → observe u x ≡ observe u y) →
  ((u : Input) (x y : State) →
    encode x ≡ encode y →
    encode (step u x) ≡ encode (step u y)) →
  (x y : State) → encode x ≡ encode y →
  TraceEquivalent step observe x y
everyStableCodecFibreIsTraceEquivalent step observe encode
  outputStable transitionStable x y same inputs =
  inputIndexedTraceDescent step observe encode
    outputStable transitionStable inputs x y same

-- One finite future witness is enough to refute a proposed codec.
futureSeparationRefutesCodec :
  ∀ {Input State Output Code : Set} →
  (step : Input → State → State) →
  (observe : Input → State → Output) →
  (encode : State → Code) →
  (x y : State) → encode x ≡ encode y →
  (inputs : List Input) →
  (trace step observe inputs x ≡ trace step observe inputs y → ⊥) →
  ((a b : State) → encode a ≡ encode b →
    TraceEquivalent step observe a b) → ⊥
futureSeparationRefutesCodec step observe encode x y same
  inputs separated sound = separated (sound x y same inputs)
