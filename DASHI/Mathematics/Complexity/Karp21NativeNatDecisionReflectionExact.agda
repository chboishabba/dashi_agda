{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeNatDecisionReflectionExact where

------------------------------------------------------------------------
-- B1/B2/B5 required ORIGINAL NatP Dec -> proof-side Nat Boolean weld.
-- The original Graph.strictAfter and validRawEdges inspect NatP._<?_,
-- NatP._≟_, while native Compare.compareLE is a bit-only Bool/ordering.
-- Explicit constructive reflection prevents an unsupported assumption
-- that these decisions are definitionally equal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; _≤_; z≤n; s≤s)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong)

originalNatStrictDecision : Nat → Nat → Bool
originalNatStrictDecision m n with NatP._<?_ m n
... | yes _ = true
... | no _ = false

originalNatEqualDecision : Nat → Nat → Bool
originalNatEqualDecision m n with NatP._≟_ m n
... | yes _ = true
... | no _ = false

natBooleanStrictWitness :
  (m n : Nat) →
  Nat._≤ᵇ_ (suc m) n ≡ true → m < n
natBooleanStrictWitness zero zero ()
natBooleanStrictWitness zero (suc n) eq = s≤s z≤n
natBooleanStrictWitness (suc m) zero ()
natBooleanStrictWitness (suc m) (suc n) eq =
  s≤s (natBooleanStrictWitness m n eq)

natStrictWitnessBoolean :
  (m n : Nat) →
  m < n → Nat._≤ᵇ_ (suc m) n ≡ true
natStrictWitnessBoolean zero zero ()
natStrictWitnessBoolean zero (suc n) proof = refl
natStrictWitnessBoolean (suc m) zero ()
natStrictWitnessBoolean (suc m) (suc n) (s≤s proof) =
  natStrictWitnessBoolean m n proof

natStrictDecisionSameBoolean :
  (m n : Nat) →
  Nat._≤ᵇ_ (suc m) n ≡ originalNatStrictDecision m n
natStrictDecisionSameBoolean m n with NatP._<?_ m n
... | yes proof = natStrictWitnessBoolean m n proof
... | no notLess with Nat._≤ᵇ_ (suc m) n in result
... | true = ⊥-elim (notLess (natBooleanStrictWitness m n result))
... | false = refl

natBooleanEqualWitness :
  (m n : Nat) →
  Nat._≡ᵇ_ m n ≡ true → m ≡ n
natBooleanEqualWitness zero zero result = refl
natBooleanEqualWitness zero (suc n) ()
natBooleanEqualWitness (suc m) zero ()
natBooleanEqualWitness (suc m) (suc n) eq =
  cong suc (natBooleanEqualWitness m n eq)

natEqualReflexive :
  (m : Nat) → Nat._≡ᵇ_ m m ≡ true
natEqualReflexive zero = refl
natEqualReflexive (suc m) = natEqualReflexive m

natEqualDecisionSameBoolean :
  (m n : Nat) →
  Nat._≡ᵇ_ m n ≡ originalNatEqualDecision m n
natEqualDecisionSameBoolean m n with NatP._≟_ m n
... | yes eq rewrite eq = natEqualReflexive n
... | no notEqual with Nat._≡ᵇ_ m n in result
... | true = ⊥-elim
  (notEqual (natBooleanEqualWitness m n result))
... | false = refl


------------------------------------------------------------------------
-- The original graph header uses NatP._≤?_ (m*3) inputSuffixLength.
-- A Boolean Nat <= test is NOT definitionally the same branch.
------------------------------------------------------------------------

originalNatLessEqualDecision : Nat → Nat → Bool
originalNatLessEqualDecision m n with NatP._≤?_ m n
... | yes _ = true
... | no _ = false

natBooleanLEWitness :
  (m n : Nat) →
  Nat._≤ᵇ_ m n ≡ true →
  _≤_ m n
natBooleanLEWitness zero n eq = z≤n
natBooleanLEWitness (suc m) zero ()
natBooleanLEWitness (suc m) (suc n) eq =
  s≤s (natBooleanLEWitness m n eq)

natLEWitnessBoolean :
  (m n : Nat) →
  _≤_ m n →
  Nat._≤ᵇ_ m n ≡ true
natLEWitnessBoolean zero n z≤n = refl
natLEWitnessBoolean (suc m) (suc n) (s≤s proof) =
  natLEWitnessBoolean m n proof

natLEDecisionSameBoolean :
  (m n : Nat) →
  Nat._≤ᵇ_ m n ≡ originalNatLessEqualDecision m n
natLEDecisionSameBoolean m n with NatP._≤?_ m n
... | yes proof = natLEWitnessBoolean m n proof
... | no notLE with Nat._≤ᵇ_ m n in answer
... | true = ⊥-elim (notLE (natBooleanLEWitness m n answer))
... | false = refl
