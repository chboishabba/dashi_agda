module DASHI.Analysis.CollatzSyracuseParityDescentEventExact where

------------------------------------------------------------------------
-- EXACT FINITE DESCENT EVENT ON THE UNIFORM PARITY-WORD CARRIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Bool.Base using (T)
open import Data.List.Base using (length)
open import Data.Nat using (_≤_; _<_; _≤ᵇ_)
import Data.Nat.Properties as NatP
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseAffineCorrectionBoundExact as Correction

------------------------------------------------------------------------
-- The finite word event that pays the multiplicative drift part of descent.
------------------------------------------------------------------------

parityDriftGood :
  {m : Nat} →
  Binary.BinaryWord m → Set
parityDriftGood {m} word =
  2 * Affine.powNat 3 (Affine.parityCount word)
  ≤ Affine.powNat 2 m

parityDriftGoodᵇ :
  {m : Nat} →
  Binary.BinaryWord m → Bool
parityDriftGoodᵇ {m} word =
  (2 * Affine.powNat 3 (Affine.parityCount word))
  ≤ᵇ Affine.powNat 2 m

parityDriftGoodᵇTrue :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  parityDriftGoodᵇ word ≡ true →
  parityDriftGood word
parityDriftGoodᵇTrue {m} word decision =
  NatP.≤ᵇ⇒≤
    (2 * Affine.powNat 3 (Affine.parityCount word))
    (Affine.powNat 2 m)
    (subst T decision tt)

parityDriftBadᵇ :
  {m : Nat} →
  Binary.BinaryWord m → Bool
parityDriftBadᵇ word with parityDriftGoodᵇ word
... | true = false
... | false = true

------------------------------------------------------------------------
-- Exact finite bad-word numerator.  No real-valued probability is introduced.
------------------------------------------------------------------------

countTrue : List Bool → Nat
countTrue [] = zero
countTrue (false ∷ tail) = countTrue tail
countTrue (true ∷ tail) = suc (countTrue tail)

badOutcomeList :
  (m : Nat) →
  List Bool
badOutcomeList m = Binary.allOutcomes (parityDriftBadᵇ {m})

badOutcomeListLength :
  (m : Nat) →
  length (badOutcomeList m) ≡ Binary.pow2Count m
badOutcomeListLength m =
  Binary.allOutcomesLength (parityDriftBadᵇ {m})

badWordCount : Nat → Nat
badWordCount m = countTrue (badOutcomeList m)

------------------------------------------------------------------------
-- Same-object descent consumer.
------------------------------------------------------------------------

goodParityWordImpliesDescent :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Affine.powNat 3 m ≤ Syracuse.toNat x →
  parityDriftGood (Itinerary.parityWord m x) →
  Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x
goodParityWordImpliesDescent = Correction.coarseParityMarginImpliesDescent

record ParityDescentEventBoundary : Set where
  constructor parityDescentEventBoundary
  field
    literalGoodEventOwned : Nat
    executableDecisionOwned : Nat
    exactBadWordNumeratorOwned : Nat
    goodEventToIntegerDescentOwned : Nat
    exponentialTailBoundOwned : Nat
    universalStoppingOwned : Nat

canonicalParityDescentEventBoundary : ParityDescentEventBoundary
canonicalParityDescentEventBoundary =
  parityDescentEventBoundary 1 1 1 1 0 0
