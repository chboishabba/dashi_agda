module DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Proof-oriented representation of the rational dyadic hat profile.
------------------------------------------------------------------------

data DyadicHatSupport : Set where
  noActiveShell : DyadicHatSupport
  oneActiveShell : Nat → DyadicHatSupport
  twoAdjacentShells : Nat → DyadicHatSupport

activeShells : DyadicHatSupport → List Nat
activeShells noActiveShell = []
activeShells (oneActiveShell j) = j ∷ []
activeShells (twoAdjacentShells j) = j ∷ suc j ∷ []

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

data AtMostTwo : Nat → Set where
  zero-at-most-two : AtMostTwo zero
  one-at-most-two : AtMostTwo (suc zero)
  two-at-most-two : AtMostTwo (suc (suc zero))

activeShellCountAtMostTwo :
  ∀ support → AtMostTwo (length (activeShells support))
activeShellCountAtMostTwo noActiveShell = zero-at-most-two
activeShellCountAtMostTwo (oneActiveShell j) = one-at-most-two
activeShellCountAtMostTwo (twoAdjacentShells j) = two-at-most-two

oneShellLength : ∀ j → length (activeShells (oneActiveShell j)) ≡ suc zero
oneShellLength j = refl

twoShellLength : ∀ j →
  length (activeShells (twoAdjacentShells j)) ≡ suc (suc zero)
twoShellLength j = refl

nearShellOverlapCountLevel : ProofLevel
nearShellOverlapCountLevel = machineChecked
