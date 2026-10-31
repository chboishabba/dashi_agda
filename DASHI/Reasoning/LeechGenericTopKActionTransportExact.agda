{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechGenericTopKActionTransportExact where

-- Generic arbitrary-E, top-k finite mathematical theorem.
-- This uses exact Nat contribution arithmetic, not float softmax.
-- A route is an ordered list of Fin E; no uniqueness is inferred.
-- Assumptions are explicit witnesses to route transport and
-- each selected expert's weighted contribution.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

cong₂ : ∀ {A B C : Set} (f : A → B → C)
        {a a' : A} {b b' : B} →
        a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

sum : List Nat → Nat
sum [] = zero
sum (x ∷ xs) = x + sum xs

weightedTotal : ∀ {E : Nat} →
                List (Fin E) → (Fin E → Nat) → Nat
weightedTotal [] contribution = zero
weightedTotal (e ∷ es) contribution =
  contribution e + weightedTotal es contribution

-- Explicit count: the caller must certify that the selected route
-- has the advertised k entries; it is never asserted for arbitrary lists.
record TopKRoute (E k : Nat) : Set where
  constructor topKRoute
  field
    entries : List (Fin E)
    exactlyK : length entries ≡ k
open TopKRoute public

-- Generic selected expert permutation and joint input/history
-- transformation require an actual contribution commutation witness.
-- This is deliberately separate from semantic opposition.
weightedTotalTransport :
  ∀ {E : Nat} →
  (route : List (Fin E)) (permutation : Fin E → Fin E) →
  (before after : Fin E → Nat) →
  ((e : Fin E) → after (permutation e) ≡ before e) →
  weightedTotal (map permutation route) after
    ≡ weightedTotal route before
weightedTotalTransport [] permutation before after witness = refl
weightedTotalTransport (e ∷ es) permutation before after witness =
  cong₂ _+_ (witness e)
    (weightedTotalTransport es permutation before after witness)

-- The selected count is preserved under map, even when the
-- permutation's bijectivity is not supplied. Bijectivity/no-duplicate
-- must be certified independently for a *genuine* expert permutation.
mapLength :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  length (map f xs) ≡ length xs
mapLength f [] = refl
mapLength f (x ∷ xs) rewrite mapLength f xs = refl

transportTopK :
  ∀ {E k : Nat} →
  (route : TopKRoute E k) →
  (permutation : Fin E → Fin E) →
  TopKRoute E k
transportTopK (topKRoute es size) permutation =
  topKRoute (map permutation es)
    (trans (mapLength permutation es) size)
  where
    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl yz = yz

transportPreservesWeightedMixture :
  ∀ {E k : Nat} →
  (route : TopKRoute E k) →
  (permutation : Fin E → Fin E) →
  (before after : Fin E → Nat) →
  ((e : Fin E) → after (permutation e) ≡ before e) →
  weightedTotal (entries (transportTopK route permutation)) after
    ≡ weightedTotal (entries route) before
transportPreservesWeightedMixture (topKRoute es size) permutation before after witness =
  weightedTotalTransport es permutation before after witness

-- With no contribution witness there is NO global symmetry theorem:
-- the learned router may select different experts under inversion.
-- Histories, state update, semantic action fitting, floating weights,
-- and remote consumer decoding require separately checked refinement.


-- Selected-only history transition over an arbitrary expert index.
-- A route/membership implementation supplies selected : Fin E → Bool.
-- An unselected expert's state is definitionally unchanged.
updateHistory :
  ∀ {E : Nat} {H : Set} →
  (selected : Fin E → Bool) →
  (old : Fin E → H) →
  (advance : Fin E → H → H) →
  Fin E → H
updateHistory selected old advance e with selected e
... | true = advance e (old e)
... | false = old e

inactiveHistoryPreserved :
  ∀ {E : Nat} {H : Set} →
  (selected : Fin E → Bool) →
  (old : Fin E → H) →
  (advance : Fin E → H → H) →
  (e : Fin E) → selected e ≡ false →
  updateHistory selected old advance e ≡ old e
inactiveHistoryPreserved selected old advance e selectedFalse
  rewrite selectedFalse = refl

-- State compatibility is a distinct, non-derivable hypothesis:
-- source routing and weighted output agreement do not suffice.
-- If s' selects mapped IDs and histories are transported by p,
-- require selected' (p e)=selected e and transitions commute.
