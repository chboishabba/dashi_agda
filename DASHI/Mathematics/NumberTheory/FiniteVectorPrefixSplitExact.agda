module DASHI.Mathematics.NumberTheory.FiniteVectorPrefixSplitExact where

------------------------------------------------------------------------
-- FINITE VECTOR PREFIX / TAIL ALGEBRA
--
-- Neutral length-indexed split machinery used to normalize ambient partition
-- multiplicity vectors.  No partition or analytic semantics occur here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

------------------------------------------------------------------------
-- Split a vector of length prefix + tail at the prefix boundary.

takePrefix :
  ∀ {A : Set} (prefix tail : Nat) →
  Vec A (prefix + tail) → Vec A prefix
takePrefix zero tail vector = []
takePrefix (suc prefix) tail (x ∷ xs) =
  x ∷ takePrefix prefix tail xs

dropPrefix :
  ∀ {A : Set} (prefix tail : Nat) →
  Vec A (prefix + tail) → Vec A tail
dropPrefix zero tail vector = vector
dropPrefix (suc prefix) tail (x ∷ xs) =
  dropPrefix prefix tail xs

appendVec :
  ∀ {A : Set} {left right : Nat} →
  Vec A left → Vec A right → Vec A (left + right)
appendVec [] ys = ys
appendVec (x ∷ xs) ys = x ∷ appendVec xs ys

splitReconstruct :
  ∀ {A : Set} (prefix tail : Nat)
    (vector : Vec A (prefix + tail)) →
  appendVec (takePrefix prefix tail vector)
    (dropPrefix prefix tail vector)
  ≡ vector
splitReconstruct zero tail vector = refl
splitReconstruct (suc prefix) tail (x ∷ xs) =
  cong (x ∷_) (splitReconstruct prefix tail xs)

------------------------------------------------------------------------
-- Shift a tail-local Fin index through a prefix.

shiftIndexBy :
  ∀ {tail : Nat} → (prefix : Nat) → Fin tail → Fin (prefix + tail)
shiftIndexBy zero index = index
shiftIndexBy (suc prefix) index = fsuc (shiftIndexBy prefix index)

shiftIndexToNat :
  ∀ {tail : Nat} (prefix : Nat) (index : Fin tail) →
  toℕ (shiftIndexBy prefix index) ≡ prefix + toℕ index
shiftIndexToNat zero index = refl
shiftIndexToNat (suc prefix) index =
  cong suc (shiftIndexToNat prefix index)

------------------------------------------------------------------------
-- Generic lookup and its compatibility with dropPrefix.

lookupVec :
  ∀ {A : Set} {n : Nat} → Fin n → Vec A n → A
lookupVec fzero (x ∷ xs) = x
lookupVec (fsuc index) (x ∷ xs) = lookupVec index xs

lookupDropPrefix :
  ∀ {A : Set} {tail : Nat}
    (prefix : Nat)
    (index : Fin tail)
    (vector : Vec A (prefix + tail)) →
  lookupVec index (dropPrefix prefix tail vector)
  ≡ lookupVec (shiftIndexBy prefix index) vector
lookupDropPrefix zero index vector = refl
lookupDropPrefix (suc prefix) index (x ∷ xs) =
  lookupDropPrefix prefix index xs

------------------------------------------------------------------------
-- Pointwise zero implies literal zero vector.

zeroVec : (n : Nat) → Vec Nat n
zeroVec zero = []
zeroVec (suc n) = zero ∷ zeroVec n

pointwiseZeroToVectorZero :
  ∀ {n : Nat} (vector : Vec Nat n) →
  (∀ index → lookupVec index vector ≡ zero) →
  vector ≡ zeroVec n
pointwiseZeroToVectorZero [] pointwise = refl
pointwiseZeroToVectorZero (x ∷ xs) pointwise =
  cong₂ _∷_
    (pointwise fzero)
    (pointwiseZeroToVectorZero xs (λ index → pointwise (fsuc index)))

------------------------------------------------------------------------
-- Elementary bound used for shifted tail weights.

prefixLessThanShiftedSuccessor :
  ∀ (prefix extra : Nat) → prefix < suc (prefix + extra)
prefixLessThanShiftedSuccessor prefix extra =
  Data.Nat.Base.s≤s (m≤m+n prefix extra)

------------------------------------------------------------------------
-- No domain semantics enter this owner.
------------------------------------------------------------------------
