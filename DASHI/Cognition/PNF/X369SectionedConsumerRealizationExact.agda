module DASHI.Cognition.PNF.X369SectionedConsumerRealizationExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Abstract total input-indexed system; rejected inputs can be represented
-- as explicitly tagged observations and identity successors.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

module Quotient {Input State Output Code : Set}
  (step : Input → State → State)
  (observe : Input → State → Output)
  (encode : State → Code)
  (section : Code → State)
  (rightInverse : (c : Code) → encode (section c) ≡ c)
  (outputStable : (u : Input) (x y : State) →
     encode x ≡ encode y → observe u x ≡ observe u y)
  (transitionStable : (u : Input) (x y : State) →
     encode x ≡ encode y → encode (step u x) ≡ encode (step u y)) where

  reducedStep : Input → Code → Code
  reducedStep u c = encode (step u (section c))

  reducedObserve : Input → Code → Output
  reducedObserve u c = observe u (section c)

  transitionDescends : (u : Input) (x : State) →
    encode (step u x) ≡ reducedStep u (encode x)
  transitionDescends u x =
    transitionStable u x (section (encode x)) (sym (rightInverse (encode x)))

  observationDescends : (u : Input) (x : State) →
    observe u x ≡ reducedObserve u (encode x)
  observationDescends u x =
    outputStable u x (section (encode x)) (sym (rightInverse (encode x)))

  traceDescends : (us : List Input) (x : State) →
    F.trace step observe us x ≡
    F.trace reducedStep reducedObserve us (encode x)
  traceDescends [] x = refl
  traceDescends (u ∷ us) x =
    F.cong₂ _∷_ (observationDescends u x)
      (trans (traceDescends us (step u x))
        (F.cong (F.trace reducedStep reducedObserve us)
          (transitionDescends u x)))

  -- A section reopens a representative, not the original fine state.
  sectionPreservesFuture : (x : State) →
    F.TraceEquivalent step observe x (section (encode x))
  sectionPreservesFuture x us =
    F.inputIndexedTraceDescent step observe encode outputStable
      transitionStable us x (section (encode x))
      (sym (rightInverse (encode x)))

module Joint {Input State O P C D : Set}
  (step : Input → State → State)
  (obs₁ : Input → State → O)
  (obs₂ : Input → State → P)
  (enc₁ : State → C)
  (enc₂ : State → D)
  (o₁ : (u : Input) (x y : State) → enc₁ x ≡ enc₁ y → obs₁ u x ≡ obs₁ u y)
  (o₂ : (u : Input) (x y : State) → enc₂ x ≡ enc₂ y → obs₂ u x ≡ obs₂ u y)
  (t₁ : (u : Input) (x y : State) → enc₁ x ≡ enc₁ y → enc₁ (step u x) ≡ enc₁ (step u y))
  (t₂ : (u : Input) (x y : State) → enc₂ x ≡ enc₂ y → enc₂ (step u x) ≡ enc₂ (step u y)) where

  Code : Set
  Code = Σ C (λ _ → D)

  Output : Set
  Output = Σ O (λ _ → P)

  encode : State → Code
  encode x = enc₁ x , enc₂ x

  observe : Input → State → Output
  observe u x = obs₁ u x , obs₂ u x

  outputStable : (u : Input) (x y : State) →
    encode x ≡ encode y → observe u x ≡ observe u y
  outputStable u x y same =
    F.cong₂ (λ a b → a , b) (o₁ u x y (F.cong fst same))
      (o₂ u x y (F.cong snd same))

  transitionStable : (u : Input) (x y : State) →
    encode x ≡ encode y → encode (step u x) ≡ encode (step u y)
  transitionStable u x y same =
    F.cong₂ (λ a b → a , b) (t₁ u x y (F.cong fst same))
      (t₂ u x y (F.cong snd same))

  jointFuture : (x y : State) → encode x ≡ encode y →
    F.TraceEquivalent step observe x y
  jointFuture x y same us =
    F.inputIndexedTraceDescent step observe encode outputStable
      transitionStable us x y same
