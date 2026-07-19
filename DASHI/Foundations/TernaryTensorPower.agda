module DASHI.Foundations.TernaryTensorPower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- The primitive carrier is ternary.  M-level labels are roles or views;
-- they are not cardinalities.  TPower n is the n-fold Cartesian product
-- of the ternary carrier.
------------------------------------------------------------------------

data Trit : Set where
  negative neutral positive : Trit

TPower : Nat → Set
TPower zero    = ⊤
TPower (suc n) = Trit × TPower n

------------------------------------------------------------------------
-- Product factorisation.
--
-- A decomposition n = m + k changes indexing/coarse-graining, not the
-- underlying state space.  append and split exhibit this directly.
------------------------------------------------------------------------

append : {m n : Nat} → TPower m → TPower n → TPower (m + n)
append {zero}  tt       ys = ys
append {suc m} (x , xs) ys = x , append xs ys

split : (m : Nat) {n : Nat} → TPower (m + n) → TPower m × TPower n
split zero    xs       = tt , xs
split (suc m) (x , xs) with split m xs
... | left , right = (x , left) , right

splitAppend :
  (m : Nat) {n : Nat} →
  (xs : TPower m) → (ys : TPower n) →
  split m (append xs ys) ≡ (xs , ys)
splitAppend zero    tt       ys = refl
splitAppend (suc m) (x , xs) ys rewrite splitAppend m xs ys = refl

appendSplit :
  (m : Nat) {n : Nat} →
  (xs : TPower (m + n)) →
  append (proj₁ (split m xs)) (proj₂ (split m xs)) ≡ xs
appendSplit zero    xs       = refl
appendSplit (suc m) (x , xs) rewrite appendSplit m xs = refl

record Iso (A B : Set) : Set where
  constructor mkIso
  field
    forward  : A → B
    backward : B → A
    backwardForward : (x : A) → backward (forward x) ≡ x
    forwardBackward : (y : B) → forward (backward y) ≡ y

factorisationIso : (m n : Nat) → Iso (TPower (m + n)) (TPower m × TPower n)
factorisationIso m n =
  mkIso
    (split m)
    (λ pair → append (proj₁ pair) (proj₂ pair))
    (appendSplit m)
    (λ pair → splitAppend m (proj₁ pair) (proj₂ pair))

------------------------------------------------------------------------
-- Canonical M-role aliases.
--
-- These names record the intended role of a coordinate, relation, and
-- closure view.  They do not assert that M6 has six states or M9 nine states.
------------------------------------------------------------------------

M3Carrier : Set
M3Carrier = TPower (suc zero)

M6RelationCarrier : Set
M6RelationCarrier = TPower (suc (suc zero))

M9ClosureCarrier : Set
M9ClosureCarrier = TPower (suc (suc (suc zero)))
