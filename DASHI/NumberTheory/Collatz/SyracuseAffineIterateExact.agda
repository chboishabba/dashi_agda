module DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact where

------------------------------------------------------------------------
-- EXACT AFFINE ITERATE NORMAL FORM
--
-- The word-side coefficient is executable here.  The integer equality is a
-- theorem-bearing source field so downstream users cannot silently assume it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary

powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc n) = base * powNat base n

parityCount : {m : Nat} → Binary.BinaryWord m → Nat
parityCount Binary.end = zero
parityCount (Binary.bit0 tail) = parityCount tail
parityCount (Binary.bit1 tail) = suc (parityCount tail)

affineAdditiveTerm : {m : Nat} → Binary.BinaryWord m → Nat
affineAdditiveTerm Binary.end = zero
affineAdditiveTerm (Binary.bit0 tail) =
  2 * affineAdditiveTerm tail
affineAdditiveTerm (Binary.bit1 tail) =
  powNat 3 (parityCount tail) + 2 * affineAdditiveTerm tail

record SyracuseAffineIterateSource : Set₁ where
  field
    syracuseAffineIterateExact :
      (m : Nat) → (x : Syracuse.PositiveNat) →
      powNat 2 m * Syracuse.toNat (Syracuse.syracuseIterate m x)
      ≡
      powNat 3 (parityCount (Itinerary.parityWord m x)) * Syracuse.toNat x
      + affineAdditiveTerm (Itinerary.parityWord m x)

open SyracuseAffineIterateSource public

-- Executable coefficient specimens.
a-zero : affineAdditiveTerm Binary.end ≡ 0
a-zero = refl

a-odd : affineAdditiveTerm (Binary.bit1 Binary.end) ≡ 1
a-odd = refl

a-even-odd :
  affineAdditiveTerm (Binary.bit0 (Binary.bit1 Binary.end)) ≡ 2
a-even-odd = refl

a-odd-even :
  affineAdditiveTerm (Binary.bit1 (Binary.bit0 Binary.end)) ≡ 1
a-odd-even = refl

record AffineIterateBoundary : Set where
  constructor affineIterateBoundary
  field
    additiveTermExecutable : Nat
    affineIdentityMustBeSourceWritten : Nat
    parityHeuristicAloneSuffices : Nat

canonicalAffineIterateBoundary : AffineIterateBoundary
canonicalAffineIterateBoundary = affineIterateBoundary 1 1 0
