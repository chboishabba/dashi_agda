module DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact where

------------------------------------------------------------------------
-- FINITE NAT VECTOR COORDINATE UPDATE ALGEBRA
--
-- Cross-pollinated from the repo's many finite-coordinate carriers.  This
-- neutral owner supplies exactly the update algebra needed by the Erdos
-- multiplicity deletion map: add/subtract a natural number at one Fin-indexed
-- coordinate, identify the updated lookup, and prove the two round trips.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (_≤_; _∸_)
open import Data.Nat.Properties using (m∸n+n≡m; m+n∸n≡m)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

lookupNat : ∀ {n : Nat} → Fin n → Vec Nat n → Nat
lookupNat fzero (x ∷ xs) = x
lookupNat (fsuc index) (x ∷ xs) = lookupNat index xs

addAt :
  ∀ {n : Nat} → Nat → Fin n → Vec Nat n → Vec Nat n
addAt amount fzero (x ∷ xs) = (x + amount) ∷ xs
addAt amount (fsuc index) (x ∷ xs) =
  x ∷ addAt amount index xs

subtractAt :
  ∀ {n : Nat} → Nat → Fin n → Vec Nat n → Vec Nat n
subtractAt amount fzero (x ∷ xs) = (x ∸ amount) ∷ xs
subtractAt amount (fsuc index) (x ∷ xs) =
  x ∷ subtractAt amount index xs

lookupAddAt :
  ∀ {n : Nat}
    (amount : Nat) (index : Fin n) (vector : Vec Nat n) →
  lookupNat index (addAt amount index vector)
  ≡ lookupNat index vector + amount
lookupAddAt amount fzero (x ∷ xs) = refl
lookupAddAt amount (fsuc index) (x ∷ xs) =
  lookupAddAt amount index xs

lookupSubtractAt :
  ∀ {n : Nat}
    (amount : Nat) (index : Fin n) (vector : Vec Nat n) →
  lookupNat index (subtractAt amount index vector)
  ≡ lookupNat index vector ∸ amount
lookupSubtractAt amount fzero (x ∷ xs) = refl
lookupSubtractAt amount (fsuc index) (x ∷ xs) =
  lookupSubtractAt amount index xs

addAfterSubtractAt :
  ∀ {n : Nat}
    (amount : Nat) (index : Fin n) (vector : Vec Nat n) →
  amount ≤ lookupNat index vector →
  addAt amount index (subtractAt amount index vector) ≡ vector
addAfterSubtractAt amount fzero (x ∷ xs) available =
  cong (_∷ xs) (m∸n+n≡m available)
addAfterSubtractAt amount (fsuc index) (x ∷ xs) available =
  cong (x ∷_) (addAfterSubtractAt amount index xs available)

subtractAfterAddAt :
  ∀ {n : Nat}
    (amount : Nat) (index : Fin n) (vector : Vec Nat n) →
  subtractAt amount index (addAt amount index vector) ≡ vector
subtractAfterAddAt amount fzero (x ∷ xs) =
  cong (_∷ xs) (m+n∸n≡m x amount)
subtractAfterAddAt amount (fsuc index) (x ∷ xs) =
  cong (x ∷_) (subtractAfterAddAt amount index xs)

------------------------------------------------------------------------
-- This owner is purely finite arithmetic.  It does not know about partitions,
-- weighted mass, Bishop reals, or asymptotics.
------------------------------------------------------------------------
