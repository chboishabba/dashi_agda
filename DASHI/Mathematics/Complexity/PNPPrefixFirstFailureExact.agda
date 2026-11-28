module DASHI.Mathematics.Complexity.PNPPrefixFirstFailureExact where

-- For each fixed original assignment the clause-failure word has one
-- of two mutually exclusive constructors: survives all or first failure.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Nat.Base using (_+_)
open import Data.Product using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

data Survives : List Bool → Set where
  none : Survives []
  keep : ∀ {xs} → Survives xs → Survives (false ∷ xs)

data FirstFailure : List Bool → Nat → Set where
  here : ∀ {xs} → FirstFailure (true ∷ xs) zero
  later : ∀ {xs j} → FirstFailure xs j → FirstFailure (false ∷ xs) (suc j)

partition : (xs : List Bool) → Survives xs ⊎ Σ Nat (FirstFailure xs)
partition [] = inj₁ none
partition (true ∷ xs) = inj₂ (zero , here)
partition (false ∷ xs) with partition xs
... | inj₁ h = inj₁ (keep h)
... | inj₂ (j , h) = inj₂ (suc j , later h)

disjoint : ∀ {xs j} → Survives xs → FirstFailure xs j → ⊥
disjoint none ()
disjoint (keep h) (later e) = disjoint h e

unique : ∀ {xs i j} → FirstFailure xs i → FirstFailure xs j → i ≡ j
unique here here = refl
unique (later a) (later b) = cong suc (unique a b)

appendSurvives : ∀ {xs ys} → Survives xs → Survives ys → Survives (xs ++ ys)
appendSurvives none q = q
appendSurvives (keep p) q = keep (appendSurvives p q)

firstAfterPrefix : ∀ {xs ys j} → Survives xs → FirstFailure ys j →
  FirstFailure (xs ++ ys) (length xs + j)
firstAfterPrefix none e = e
firstAfterPrefix (keep p) e = later (firstAfterPrefix p e)

-- If the completed prefix survives, the unexpanded tail is exactly
-- the disjoint sum of its first-failure fibres, or final survival.
tailPartition : ∀ {xs} → Survives xs → (ys : List Bool) →
  Survives (xs ++ ys) ⊎ Σ Nat (λ j → FirstFailure (xs ++ ys) j)
tailPartition p ys with partition ys
... | inj₁ q = inj₁ (appendSurvives p q)
... | inj₂ (j , q) = inj₂ (_ , firstAfterPrefix p q)
