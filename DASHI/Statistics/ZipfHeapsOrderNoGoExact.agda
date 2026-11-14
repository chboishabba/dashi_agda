module DASHI.Statistics.ZipfHeapsOrderNoGoExact where

-- Reuses the source-local 27-family finite corpus and authority surface.
-- This is a finite information-loss theorem only: no theorem about all
-- natural languages, empirical scaling, or stochastic independence.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import DASHI.Statistics.ZipfFamilyFiniteExact as Family

isFalse : Bool → Bool
isFalse true = false
isFalse false = true

record TwoTypeHistogram : Set where
  constructor histogram
  field
    positiveCount : Nat
    negativeCount : Nat

observedHistogram : List Bool → TwoTypeHistogram
observedHistogram xs = histogram
  (Family.countIf (λ b → b) xs)
  (Family.countIf isFalse xs)

grouped : List Bool
grouped = true ∷ true ∷ false ∷ false ∷ []

alternating : List Bool
alternating = true ∷ false ∷ true ∷ false ∷ []

sameHistogram : observedHistogram grouped ≡ observedHistogram alternating
sameHistogram = refl

seenTrue : List Bool → Bool
seenTrue [] = false
seenTrue (true ∷ xs) = true
seenTrue (false ∷ xs) = seenTrue xs

seenFalse : List Bool → Bool
seenFalse [] = false
seenFalse (false ∷ xs) = true
seenFalse (true ∷ xs) = seenFalse xs

indicator : Bool → Nat
indicator false = zero
indicator true = suc zero

distinctTypes : List Bool → Nat
distinctTypes xs = indicator (seenTrue xs) + indicator (seenFalse xs)

takeTwo : List Bool → List Bool
takeTwo [] = []
takeTwo (a ∷ []) = a ∷ []
takeTwo (a ∷ b ∷ xs) = a ∷ b ∷ []

heapsAtTwo : List Bool → Nat
heapsAtTwo xs = distinctTypes (takeTwo xs)

groupedPrefixHasOneType : heapsAtTwo grouped ≡ suc zero
groupedPrefixHasOneType = refl

alternatingPrefixHasTwoTypes : heapsAtTwo alternating ≡ suc (suc zero)
alternatingPrefixHasTwoTypes = refl

data ⊥ : Set where

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl yz = yz

oneNotTwo : suc zero ≡ suc (suc zero) → ⊥
oneNotTwo ()

-- An exact same-histogram pair with different prefix-type counts excludes
-- any deterministic estimator from histogram alone, even if the histogram
-- admits an exact Zipf fit. Assumptions about token order are indispensable.
histogramDoesNotDetermineHeapsPrefix :
  (predict : TwoTypeHistogram → Nat) →
  ((xs : List Bool) → predict (observedHistogram xs) ≡ heapsAtTwo xs) → ⊥
histogramDoesNotDetermineHeapsPrefix predict correct =
  oneNotTwo (transEq (symEq (correct grouped)) (correct alternating))
