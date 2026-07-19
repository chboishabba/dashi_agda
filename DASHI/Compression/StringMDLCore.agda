module DASHI.Compression.StringMDLCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_<_ ; _≤_)

------------------------------------------------------------------------
-- Exact string-corpus MDL substrate.
--
-- This module deliberately does not identify lemmas, canonical words, or
-- semantic roots.  A dictionary atom is only a reusable string factor.
------------------------------------------------------------------------

CodeLength : Set
CodeLength = Nat

record StringMDLSystem : Set₂ where
  field
    Corpus Dictionary Segmentation State Move : Set

    corpus       : State → Corpus
    dictionary   : State → Dictionary
    segmentation : State → Segmentation

    -- Exact two-part code length L(D) + L(C | D , sigma).
    dictionaryLength : Dictionary → CodeLength
    corpusLength     : Corpus → Dictionary → Segmentation → CodeLength

    totalLength : State → CodeLength
    totalLengthLaw :
      ∀ s →
      totalLength s ≡
        dictionaryLength (dictionary s) +
        corpusLength (corpus s) (dictionary s) (segmentation s)

    -- The surface corpus carried by a state and its exact reconstruction.
    sourceText : State → String
    decodeText : State → String
    reconstructs : ∀ s → decodeText s ≡ sourceText s

    -- Move semantics are exact and remain independent of proposal order.
    Admissible : State → Move → Set
    apply      : State → Move → State

    corpusPreserved :
      ∀ s m → Admissible s m → corpus (apply s m) ≡ corpus s

    sourcePreserved :
      ∀ s m → Admissible s m → sourceText (apply s m) ≡ sourceText s

open StringMDLSystem public

------------------------------------------------------------------------
-- Exact acceptance witnesses.
------------------------------------------------------------------------

record ExactImprovement (M : StringMDLSystem) (s : State M) : Set where
  field
    move       : Move M
    admissible : Admissible M s move
    strictMDL  : totalLength M (apply M s move) < totalLength M s

open ExactImprovement public

record NonWorseningMove (M : StringMDLSystem) (s : State M) : Set where
  field
    move       : Move M
    admissible : Admissible M s move
    weakMDL    : totalLength M (apply M s move) ≤ totalLength M s

open NonWorseningMove public

accepted-reconstructs :
  (M : StringMDLSystem) →
  (s : State M) →
  (i : ExactImprovement M s) →
  decodeText M (apply M s (move i)) ≡ sourceText M (apply M s (move i))
accepted-reconstructs M s i = reconstructs M (apply M s (move i))

accepted-preserves-source :
  (M : StringMDLSystem) →
  (s : State M) →
  (i : ExactImprovement M s) →
  sourceText M (apply M s (move i)) ≡ sourceText M s
accepted-preserves-source M s i = sourcePreserved M s (move i) (admissible i)

accepted-strictly-descends :
  (M : StringMDLSystem) →
  (s : State M) →
  (i : ExactImprovement M s) →
  totalLength M (apply M s (move i)) < totalLength M s
accepted-strictly-descends M s i = strictMDL i

------------------------------------------------------------------------
-- Search-family honesty.
--
-- Global optimality is always relative to an explicit candidate family.
------------------------------------------------------------------------

record CandidateFamily (M : StringMDLSystem) : Set₁ where
  field
    Candidate : Set
    realize   : Candidate → State M
    familyCost : Candidate → CodeLength

open CandidateFamily public

record FamilyMinimum (M : StringMDLSystem) (F : CandidateFamily M) : Set₁ where
  field
    witness : Candidate F
    minimal :
      ∀ c →
      familyCost F witness + totalLength M (realize F witness) ≤
      familyCost F c       + totalLength M (realize F c)

open FamilyMinimum public

------------------------------------------------------------------------
-- Explicit non-promotion boundary.
------------------------------------------------------------------------

record StringMDLBoundary : Set where
  field
    compressionOnly             : Bool
    compressionOnlyIsTrue       : compressionOnly ≡ true
    semanticCanonicalization    : Bool
    semanticCanonicalizationFalse : semanticCanonicalization ≡ false
    unboundedGlobalOptimumClaim : Bool
    unboundedGlobalOptimumFalse : unboundedGlobalOptimumClaim ≡ false

canonicalStringMDLBoundary : StringMDLBoundary
canonicalStringMDLBoundary =
  record
    { compressionOnly = true
    ; compressionOnlyIsTrue = Agda.Builtin.Equality.refl
    ; semanticCanonicalization = false
    ; semanticCanonicalizationFalse = Agda.Builtin.Equality.refl
    ; unboundedGlobalOptimumClaim = false
    ; unboundedGlobalOptimumFalse = Agda.Builtin.Equality.refl
    }
