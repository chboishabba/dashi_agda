module DASHI.Mathematics.Complexity.FiniteWordSizeExact where

------------------------------------------------------------------------
-- CONCRETE FINITE-WORD SIZE METRIC
--
-- The abstract PolynomialCostModel deliberately does not choose an encoding.
-- This owner supplies the standard finite Boolean-word carrier and its literal
-- length/encoding-size coordinates so later machine/Cook--Levin owners can
-- state polynomial bounds against an actual Nat-valued input size.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

BitWord : Set
BitWord = List Bool

wordLength : BitWord → Nat
wordLength [] = zero
wordLength (_ ∷ bits) = suc (wordLength bits)

encodingSize : BitWord → Nat
encodingSize = wordLength

emptyWordLength : wordLength [] ≡ zero
emptyWordLength = refl

consWordLength :
  ∀ bit bits →
  wordLength (bit ∷ bits) ≡ suc (wordLength bits)
consWordLength bit bits = refl

encodingSizeIsLength :
  ∀ word →
  encodingSize word ≡ wordLength word
encodingSizeIsLength word = refl

record ConcreteWordSizeMetric : Set₁ where
  field
    Word : Set
    inputLength : Word → Nat
    encodedSize : Word → Nat
    encodedSizeExact : ∀ word → encodedSize word ≡ inputLength word

canonicalBooleanWordSizeMetric : ConcreteWordSizeMetric
canonicalBooleanWordSizeMetric = record
  { Word = BitWord
  ; inputLength = wordLength
  ; encodedSize = encodingSize
  ; encodedSizeExact = encodingSizeIsLength
  }
