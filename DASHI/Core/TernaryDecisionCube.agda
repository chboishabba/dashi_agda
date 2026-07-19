module DASHI.Core.TernaryDecisionCube where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)

------------------------------------------------------------------------
-- A decision space may have arbitrarily many axes.  This module fixes
-- three axes only to expose the 3 × 3 × 3 carrier used by the dog-walk
-- example.  Ternarity is per-axis; it is not a claim that the whole
-- latent decision space contains only three states.

record Cube3 : Set where
  constructor cube3
  field
    axis₁ : Trit
    axis₂ : Trit
    axis₃ : Trit

open Cube3 public

invertCube : Cube3 → Cube3
invertCube (cube3 a b c) = cube3 (inv a) (inv b) (inv c)

invertCube-involutive : ∀ q → invertCube (invertCube q) ≡ q
invertCube-involutive (cube3 neg neg neg) = refl
invertCube-involutive (cube3 neg neg zer) = refl
invertCube-involutive (cube3 neg neg pos) = refl
invertCube-involutive (cube3 neg zer neg) = refl
invertCube-involutive (cube3 neg zer zer) = refl
invertCube-involutive (cube3 neg zer pos) = refl
invertCube-involutive (cube3 neg pos neg) = refl
invertCube-involutive (cube3 neg pos zer) = refl
invertCube-involutive (cube3 neg pos pos) = refl
invertCube-involutive (cube3 zer neg neg) = refl
invertCube-involutive (cube3 zer neg zer) = refl
invertCube-involutive (cube3 zer neg pos) = refl
invertCube-involutive (cube3 zer zer neg) = refl
invertCube-involutive (cube3 zer zer zer) = refl
invertCube-involutive (cube3 zer zer pos) = refl
invertCube-involutive (cube3 zer pos neg) = refl
invertCube-involutive (cube3 zer pos zer) = refl
invertCube-involutive (cube3 zer pos pos) = refl
invertCube-involutive (cube3 pos neg neg) = refl
invertCube-involutive (cube3 pos neg zer) = refl
invertCube-involutive (cube3 pos neg pos) = refl
invertCube-involutive (cube3 pos zer neg) = refl
invertCube-involutive (cube3 pos zer zer) = refl
invertCube-involutive (cube3 pos zer pos) = refl
invertCube-involutive (cube3 pos pos neg) = refl
invertCube-involutive (cube3 pos pos zer) = refl
invertCube-involutive (cube3 pos pos pos) = refl

------------------------------------------------------------------------
-- Full carrier enumeration.

allCube3 : List Cube3
allCube3 =
  cube3 neg neg neg ∷ cube3 neg neg zer ∷ cube3 neg neg pos ∷
  cube3 neg zer neg ∷ cube3 neg zer zer ∷ cube3 neg zer pos ∷
  cube3 neg pos neg ∷ cube3 neg pos zer ∷ cube3 neg pos pos ∷
  cube3 zer neg neg ∷ cube3 zer neg zer ∷ cube3 zer neg pos ∷
  cube3 zer zer neg ∷ cube3 zer zer zer ∷ cube3 zer zer pos ∷
  cube3 zer pos neg ∷ cube3 zer pos zer ∷ cube3 zer pos pos ∷
  cube3 pos neg neg ∷ cube3 pos neg zer ∷ cube3 pos neg pos ∷
  cube3 pos zer neg ∷ cube3 pos zer zer ∷ cube3 pos zer pos ∷
  cube3 pos pos neg ∷ cube3 pos pos zer ∷ cube3 pos pos pos ∷ []

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

allCube3-has-27-states :
  length allCube3 ≡
  suc (suc (suc (suc (suc (suc (suc (suc (suc
  (suc (suc (suc (suc (suc (suc (suc (suc (suc
  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))
allCube3-has-27-states = refl

------------------------------------------------------------------------
-- Operational quotient.
--
-- James's objection is represented exactly here: for a decision that
-- asks only whether the action proceeds, neutral and positive collapse.
-- This quotient does not identify the underlying Trit values.

data Act : Set where
  blocked proceed : Act

decide : Trit → Act
decide neg = blocked
decide zer = proceed
decide pos = proceed

neutral-and-positive-act-the-same : decide zer ≡ decide pos
neutral-and-positive-act-the-same = refl

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

neutral-is-not-positive : zer ≢ pos
neutral-is-not-positive ()

record OperationalQuotient : Set where
  constructor operationalQuotient
  field
    latent : Cube3
    action : Act

quotientOn₁ : Cube3 → OperationalQuotient
quotientOn₁ q = operationalQuotient q (decide (axis₁ q))
