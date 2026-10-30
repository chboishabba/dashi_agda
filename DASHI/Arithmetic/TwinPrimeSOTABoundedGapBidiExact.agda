{-# OPTIONS --safe #-}
module DASHI.Arithmetic.TwinPrimeSOTABoundedGapBidiExact where

------------------------------------------------------------------------
-- SOTA PRIME-GAP BIDIRECTIONAL BRIDGE / PROVENANCE, 31 Oct 2026.
--
-- Original research roots:
--  Goldston-Pintz-Yildirim, Zhang (2013/2014), Maynard-Tao,
--  DHJ Polymath 8b (2014): unconditional gap bound 246.
--  Axiom Math / PrimeGapsLib (2026): Lean bounded-gap formalisation.
--  OpenAI PrimeGaps186 (Aug 2026): explicit conditional Lean proof of
--  gap <=186 from THREE unformalised input axioms / certificates.
--  Chen (1973): prime + almost-prime; not a gap-2 prime pair.
--
-- This source does NOT import a theorem from another Lean project
-- without translating its exact assumptions. No comparison among
-- 246, 186 and 2 yields exact gap 2 by arithmetic alone.
--
-- Reuse original DASHI TwinPrimeSixWheelExact / certified enumerator.
-- This module closes the actual two-way semantic boundary at exact
-- shift TWO, and makes explicit that 'bounded <=B' loses exact
-- shift information. Retaining shift is the arithmetic residual.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst)
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import Data.Nat using (_≤_; _+_; z≤n; s≤s)
import Data.Nat.Primality as NatPrimality using (Prime)

-- The original bounded-prime-pair owner already contains each Nat
-- primality certificate AND its exact offset. Use its record instead
-- of constructing a parallel prime predicate.
exactGapTwoPair :
  (n : Nat) -> Twin.TwinPrimeAt n -> Twin.BoundedPrimePair Twin.two n
exactGapTwoPair n (left , right) =
  Twin.boundedPrimePair
    Twin.two
    (s≤s z≤n)
    (s≤s (s≤s z≤n))
    left right

-- Selecting an *actual* offset-two witness is enough. The offset
-- equality cannot be inferred from a coarse <=186 or <=246 bound.
boundedPairExactShiftToTwin :
  (n : Nat) ->
  (pair : Twin.BoundedPrimePair Twin.two n) ->
  Twin.BoundedPrimePair.shift pair ≡ Twin.two ->
  Twin.TwinPrimeAt n
boundedPairExactShiftToTwin n pair shiftTwo =
  Twin.BoundedPrimePair.startIsPrime pair ,
  subst
    (λ shift -> NatPrimality.Prime (n + shift))
    shiftTwo
    (Twin.BoundedPrimePair.endIsPrime pair)

-- The exact gap-two certificate is equivalent to a bounded-pair
-- certificate PLUS the retained exact shift-two fibre.
record GapTwoBoundedFibre (n : Nat) : Set where
  constructor gap-two-bounded-fibre
  field
    bounded : Twin.BoundedPrimePair Twin.two n
    exactShift : Twin.BoundedPrimePair.shift bounded ≡ Twin.two

twinToSOTAGapTwoFibre :
  (n : Nat) -> Twin.TwinPrimeAt n -> GapTwoBoundedFibre n
twinToSOTAGapTwoFibre n twin =
  gap-two-bounded-fibre (exactGapTwoPair n twin) refl

sotaGapTwoFibreToTwin :
  (n : Nat) -> GapTwoBoundedFibre n -> Twin.TwinPrimeAt n
sotaGapTwoFibreToTwin n certificate =
  boundedPairExactShiftToTwin n
    (GapTwoBoundedFibre.bounded certificate)
    (GapTwoBoundedFibre.exactShift certificate)

-- Unbounded versions. The forward direction inherits an existing
-- proof. The converse requires a cofinal bounded witness at EXACT 2.
-- An arbitrary bounded <=246 or <=186 prime pair is insufficient.
cofinalGapTwoFibreImpliesTwins :
  ((N : Nat) ->
    Σ Nat (λ n -> (N ≤ n) × GapTwoBoundedFibre n)) ->
  Twin.TwinPrimesInfinitelyOften
cofinalGapTwoFibreImpliesTwins family N with family N
... | n , (above , located) =
  n , (above , sotaGapTwoFibreToTwin n located)

twinsGiveCofinalGapTwoFibre :
  Twin.TwinPrimesInfinitelyOften ->
  (N : Nat) ->
  Σ Nat (λ n -> (N ≤ n) × GapTwoBoundedFibre n)
twinsGiveCofinalGapTwoFibre twins N with twins N
... | n , (above , twin) =
  n , (above , twinToSOTAGapTwoFibre n twin)
