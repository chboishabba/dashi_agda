module DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact where

------------------------------------------------------------------------
-- PARITY WORD <-> INTEGER RESIDUE CYLINDER
--
-- This module owns the exact theorem interface.  It deliberately does not use
-- cardinality equality as a substitute for forward/reverse same-object proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.DivMod using (_%_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary

pow2 : Nat → Nat
pow2 0 = 1
pow2 (suc n) = 2 * pow2 n
  where open import Agda.Builtin.Nat using (_*_)

record ParityCylinderSource : Set₁ where
  field
    residueOfParityWord :
      {m : Nat} → Binary.BinaryWord m → Nat

    residueBounded :
      {m : Nat} → (word : Binary.BinaryWord m) →
      residueOfParityWord word % pow2 m ≡ residueOfParityWord word

    parityWordImpliesResidue :
      {m : Nat} → (word : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Itinerary.parityWord m x ≡ word →
      Syracuse.toNat x % pow2 m ≡ residueOfParityWord word

    residueImpliesParityWord :
      {m : Nat} → (word : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Syracuse.toNat x % pow2 m ≡ residueOfParityWord word →
      Itinerary.parityWord m x ≡ word

    residueOfParityWordInjective :
      {m : Nat} → (left right : Binary.BinaryWord m) →
      residueOfParityWord left ≡ residueOfParityWord right →
      left ≡ right

open ParityCylinderSource public

parityCylinderIff :
  (source : ParityCylinderSource) →
  {m : Nat} → (word : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  (Itinerary.parityWord m x ≡ word →
    Syracuse.toNat x % pow2 m ≡ residueOfParityWord source word)
  ×
  (Syracuse.toNat x % pow2 m ≡ residueOfParityWord source word →
    Itinerary.parityWord m x ≡ word)
parityCylinderIff source word x =
  parityWordImpliesResidue source word x ,
  residueImpliesParityWord source word x
  where open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- The source is intentionally an explicit producer.  An inhabitant requires
-- the actual modular arithmetic proof; exhaustive finite tests are evidence,
-- not a replacement for these fields.
------------------------------------------------------------------------

record ParityCylinderBoundary : Set where
  constructor parityCylinderBoundary
  field
    cardinalityCoincidenceSuffices : Nat
    forwardProofRequired : Nat
    reverseProofRequired : Nat
    uniquenessProofRequired : Nat

canonicalParityCylinderBoundary : ParityCylinderBoundary
canonicalParityCylinderBoundary = parityCylinderBoundary 0 1 1 1
