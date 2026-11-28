module DASHI.Cognition.PNF.X369RadixHistoryExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Reuses the numeric proof pattern of PNPStandardStackCandidateRunExact
-- PR #1548 at 2545673. No dependency on an unmerged PNP branch.
-- Stack lists are newest-first; chronological lists are their reversal.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Data.Nat.DivMod using
  (_/_; _%_; [m+kn]%n≡m%n; m<n⇒m%n≡m; m<n⇒m/n≡0;
   m*n/n≡m; +-distrib-/-∣ʳ)
open import Data.Nat.Divisibility using (divides)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (trans)
import DASHI.Cognition.PNF.X369OrderedBlockCompositionExact as W

module Radix {Literal : Set}
  (baseMinusTwo : Nat)
  (digit : Literal → Nat)
  (symbol : Nat → Literal)
  (digitBound : ∀ a → digit a < suc (suc baseMinusTwo))
  (decodeDigit : ∀ a → symbol (digit a) ≡ a) where

  base = suc (suc baseMinusTwo)

  value : List Literal → Nat
  value [] = zero
  value (a ∷ xs) = digit a + base * value xs

  remainder : ∀ a xs → value (a ∷ xs) % base ≡ digit a
  remainder a xs rewrite N.*-comm base (value xs) =
    trans ([m+kn]%n≡m%n (digit a) (value xs) base)
      (m<n⇒m%n≡m (digitBound a))

  quotient : ∀ a xs → value (a ∷ xs) / base ≡ value xs
  quotient a xs rewrite N.*-comm base (value xs)
    | +-distrib-/-∣ʳ (digit a) (divides (value xs) refl)
    | m<n⇒m/n≡0 (digitBound a)
    | m*n/n≡m (value xs) base = refl

  decode : Nat → Nat → List Literal
  decode zero v = []
  decode (suc n) v = symbol (v % base) ∷ decode n (v / base)

  decodeExact : ∀ xs → decode (W.extent xs) (value xs) ≡ xs
  decodeExact [] = refl
  decodeExact (a ∷ xs)
    rewrite remainder a xs | quotient a xs | decodeDigit a | decodeExact xs = refl

  -- Extent is supplied explicitly, so zero digits are not discarded.
  reverse : List Literal → List Literal
  reverse [] = []
  reverse (a ∷ xs) = reverse xs W.++ (a ∷ [])

  chronologicalDecodeExact : ∀ xs →
    decode (W.extent (reverse xs)) (value (reverse xs)) ≡ reverse xs
  chronologicalDecodeExact xs = decodeExact (reverse xs)
