module DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact where

------------------------------------------------------------------------
-- PARITY ITINERARY OF THE LITERAL SYRACUSE ORBIT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.DivMod using (_%_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse

parity : Syracuse.PositiveNat → Bool
parity x with Syracuse.toNat x % 2
... | zero = false
... | suc _ = true

epsilon : Nat → Syracuse.PositiveNat → Bool
epsilon zero x = parity x
epsilon (suc j) x = epsilon j (Syracuse.shortcutSyracuse x)

epsilonShift :
  (j : Nat) → (x : Syracuse.PositiveNat) →
  epsilon j (Syracuse.shortcutSyracuse x) ≡ epsilon (suc j) x
epsilonShift j x = refl

parityWord :
  (m : Nat) → Syracuse.PositiveNat → Binary.BinaryWord m
parityWord zero x = Binary.end
parityWord (suc m) x with parity x
... | false = Binary.bit0 (parityWord m (Syracuse.shortcutSyracuse x))
... | true  = Binary.bit1 (parityWord m (Syracuse.shortcutSyracuse x))

parityPrefix = parityWord

dropHead :
  {m : Nat} → Binary.BinaryWord (suc m) → Binary.BinaryWord m
dropHead (Binary.bit0 tail) = tail
dropHead (Binary.bit1 tail) = tail

parityWordShift :
  (m : Nat) → (x : Syracuse.PositiveNat) →
  dropHead (parityWord (suc m) x)
  ≡ parityWord m (Syracuse.shortcutSyracuse x)
parityWordShift m x with parity x
... | false = refl
... | true = refl

firstParityFalse :
  {m : Nat} → (x : Syracuse.PositiveNat) →
  parity x ≡ false →
  parityWord (suc m) x
  ≡ Binary.bit0 (parityWord m (Syracuse.shortcutSyracuse x))
firstParityFalse x p rewrite p = refl

firstParityTrue :
  {m : Nat} → (x : Syracuse.PositiveNat) →
  parity x ≡ true →
  parityWord (suc m) x
  ≡ Binary.bit1 (parityWord m (Syracuse.shortcutSyracuse x))
firstParityTrue x p rewrite p = refl

-- Small orientation witnesses.
word1-at-one : parityWord 1 Syracuse.one ≡ Binary.bit1 Binary.end
word1-at-one = refl

word2-at-one :
  parityWord 2 Syracuse.one ≡ Binary.bit1 (Binary.bit0 Binary.end)
word2-at-one = refl

word3-at-three :
  parityWord 3 Syracuse.three
  ≡ Binary.bit1 (Binary.bit1 (Binary.bit0 Binary.end))
word3-at-three = refl
