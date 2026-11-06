{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact where

------------------------------------------------------------------------
-- K05 N21: ACTUAL FINITE BIT-WORD EQUALITY PRIMITIVE.
--
-- This is a concrete recursive Boolean-word comparator with:
--   * total equality Boolean,
--   * literal extensional proof for all bit words,
--   * exact counted bit-inspection schedule,
--   * input-length upper bound, including malformed unequal lengths.
--
-- This module proves its own bitword semantics; bridging the ACTUAL
-- original gamma reader's decoded Nat endpoint equality to this
-- bitword comparator remains a separate same-value theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

bitEqual : Bool → Bool → Bool
bitEqual false false = true
bitEqual true true = true
bitEqual false true = false
bitEqual true false = false

bitEqualRefl : (bit : Bool) → bitEqual bit bit ≡ true
bitEqualRefl false = refl
bitEqualRefl true = refl

bitEqualSound :
  (a b : Bool) → bitEqual a b ≡ true → a ≡ b
bitEqualSound false false eq = refl
bitEqualSound false true ()
bitEqualSound true false ()
bitEqualSound true true eq = refl

andBool : Bool → Bool → Bool
andBool true x = x
andBool false x = false

andBoolLeft :
  (a b : Bool) → andBool a b ≡ true → a ≡ true
andBoolLeft true b proof = refl
andBoolLeft false b ()

andBoolRight :
  (a b : Bool) → andBool a b ≡ true → b ≡ true
andBoolRight true b proof = proof
andBoolRight false b ()

equalBitWords : Word.BitWord → Word.BitWord → Bool
equalBitWords [] [] = true
equalBitWords [] (_ ∷ _) = false
equalBitWords (_ ∷ _) [] = false
equalBitWords (a ∷ xs) (b ∷ ys) =
  andBool (bitEqual a b) (equalBitWords xs ys)

bitWordEqualityReflexive :
  (xs : Word.BitWord) → equalBitWords xs xs ≡ true
bitWordEqualityReflexive [] = refl
bitWordEqualityReflexive (x ∷ xs)
  rewrite bitEqualRefl x | bitWordEqualityReflexive xs = refl

bitWordEqualitySound :
  (xs ys : Word.BitWord) →
  equalBitWords xs ys ≡ true → xs ≡ ys
bitWordEqualitySound [] [] proof = refl
bitWordEqualitySound [] (_ ∷ _) ()
bitWordEqualitySound (_ ∷ _) [] ()
bitWordEqualitySound (x ∷ xs) (y ∷ ys) proof =
  trans
    (cong (λ v → v ∷ xs)
      (bitEqualSound x y
        (andBoolLeft (bitEqual x y) (equalBitWords xs ys) proof)))
    (cong (y ∷_)
      (bitWordEqualitySound xs ys
        (andBoolRight (bitEqual x y) (equalBitWords xs ys) proof)))

-- Count ONE primitive inspection per paired bit position and one
-- end-marker check. This is an exact schedule for this implementation.
bitEqualityInspectionCount :
  Word.BitWord → Word.BitWord → Nat
bitEqualityInspectionCount [] [] = 1
bitEqualityInspectionCount [] (_ ∷ _) = 1
bitEqualityInspectionCount (_ ∷ _) [] = 1
bitEqualityInspectionCount (_ ∷ xs) (_ ∷ ys) =
  suc (bitEqualityInspectionCount xs ys)

bitEqualityInspectionBound :
  (xs ys : Word.BitWord) →
  bitEqualityInspectionCount xs ys ≤ suc (Word.encodingSize xs)
bitEqualityInspectionBound [] [] = s≤s z≤n
bitEqualityInspectionBound [] (_ ∷ _) = s≤s z≤n
bitEqualityInspectionBound (_ ∷ xs) [] = s≤s z≤n
bitEqualityInspectionBound (_ ∷ xs) (_ ∷ ys) =
  s≤s (bitEqualityInspectionBound xs ys)

literalLengthIsWordSize :
  (xs : Word.BitWord) → length xs ≡ Word.encodingSize xs
literalLengthIsWordSize [] = refl
literalLengthIsWordSize (_ ∷ xs)
  rewrite literalLengthIsWordSize xs = refl

bitEqualityIndependentOfEncodedNatMagnitude :
  (xs ys : Word.BitWord) →
  bitEqualityInspectionCount xs ys ≤ suc (length xs)
bitEqualityIndependentOfEncodedNatMagnitude xs ys =
  subst
    (λ n → bitEqualityInspectionCount xs ys ≤ suc n)
    (sym (literalLengthIsWordSize xs))
    (bitEqualityInspectionBound xs ys)
