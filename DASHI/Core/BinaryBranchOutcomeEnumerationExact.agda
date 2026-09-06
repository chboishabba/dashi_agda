module DASHI.Core.BinaryBranchOutcomeEnumerationExact where

------------------------------------------------------------------------
-- COMPLETE BINARY BRANCH-OUTCOME ENUMERATION
--
-- Enumerate all words of a fixed binary branch length and map them directly to
-- Bool outcomes (true=survives, false=killed).  The resulting list has exactly
-- 2^m entries, every branch word's outcome occurs, and a chosen killed word
-- therefore supplies `false ∈ outcomes` for the finite survivor-count theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (_++_; length)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Relation.Binary.PropositionalEquality using (cong; subst)

------------------------------------------------------------------------
-- Indexed binary words.
------------------------------------------------------------------------

data BinaryWord : Nat → Set where
  end : BinaryWord zero
  bit0 : ∀ {n} → BinaryWord n → BinaryWord (suc n)
  bit1 : ∀ {n} → BinaryWord n → BinaryWord (suc n)

pow2Count : Nat → Nat
pow2Count zero = 1
pow2Count (suc n) = pow2Count n + pow2Count n

------------------------------------------------------------------------
-- Small list lemmas kept local to avoid depending on naming variants.
------------------------------------------------------------------------

lengthAppend :
  {A : Set} →
  (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
lengthAppend [] ys = refl
lengthAppend (x ∷ xs) ys = cong suc (lengthAppend xs ys)

memberAppendLeft :
  {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs → x ∈ (xs ++ ys)
memberAppendLeft here = here
memberAppendLeft (there membership) = there (memberAppendLeft membership)

memberAppendRight :
  {A : Set} {x : A} {xs ys : List A} →
  x ∈ ys → x ∈ (xs ++ ys)
memberAppendRight {xs = []} membership = membership
memberAppendRight {xs = _ ∷ xs} membership =
  there (memberAppendRight {xs = xs} membership)

------------------------------------------------------------------------
-- Enumerate outcomes without first materialising a separate word list.
------------------------------------------------------------------------

allOutcomes :
  {n : Nat} →
  (BinaryWord n → Bool) →
  List Bool
allOutcomes {zero} outcome = outcome end ∷ []
allOutcomes {suc n} outcome =
  allOutcomes (λ word → outcome (bit0 word))
  ++
  allOutcomes (λ word → outcome (bit1 word))

allOutcomesLength :
  {n : Nat} →
  (outcome : BinaryWord n → Bool) →
  length (allOutcomes outcome) ≡ pow2Count n
allOutcomesLength {zero} outcome = refl
allOutcomesLength {suc n} outcome
  rewrite
    lengthAppend
      (allOutcomes (λ word → outcome (bit0 word)))
      (allOutcomes (λ word → outcome (bit1 word)))
  | allOutcomesLength (λ word → outcome (bit0 word))
  | allOutcomesLength (λ word → outcome (bit1 word))
  = refl

chosenOutcomeOccurs :
  {n : Nat} →
  (outcome : BinaryWord n → Bool) →
  (word : BinaryWord n) →
  outcome word ∈ allOutcomes outcome
chosenOutcomeOccurs {zero} outcome end = here
chosenOutcomeOccurs {suc n} outcome (bit0 word) =
  memberAppendLeft
    (chosenOutcomeOccurs
      (λ suffix → outcome (bit0 suffix))
      word)
chosenOutcomeOccurs {suc n} outcome (bit1 word) =
  memberAppendRight
    (chosenOutcomeOccurs
      (λ suffix → outcome (bit1 suffix))
      word)

chosenKilledWordGivesFalseMember :
  {n : Nat} →
  (outcome : BinaryWord n → Bool) →
  (word : BinaryWord n) →
  outcome word ≡ false →
  false ∈ allOutcomes outcome
chosenKilledWordGivesFalseMember outcome word killed =
  subst
    (λ value → value ∈ allOutcomes outcome)
    killed
    (chosenOutcomeOccurs outcome word)
