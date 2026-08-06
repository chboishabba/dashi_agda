module DASHI.Physics.Closure.NSTriadKNLuoFiniteHalfShellPartitionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Construct the literal finite dyadic split at r=q/2 used in Luo Section 4.
-- Division is avoided: the lower region is represented by 2r<=q and the
-- upper region by its decidable negation.  Every indexed shell sample is sent
-- to exactly one evidence-carrying list, and the two amplitude folds are
-- proved to reconstruct the original fold.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (¬_; yes; no)

record IndexedShellValue : Set where
  constructor indexed-shell
  field
    shellIndex : Nat
    amplitude : ℚ

open IndexedShellValue public

record LowerHalfSample (outputShell : Nat) : Set where
  constructor lower-half-sample
  field
    lowerSample : IndexedShellValue
    twiceIndexAtMostOutput :
      shellIndex lowerSample + shellIndex lowerSample ≤ outputShell

open LowerHalfSample public

record UpperHalfSample (outputShell : Nat) : Set where
  constructor upper-half-sample
  field
    upperSample : IndexedShellValue
    twiceIndexNotAtMostOutput :
      ¬ (shellIndex upperSample + shellIndex upperSample ≤ outputShell)

open UpperHalfSample public

record HalfShellSplit (outputShell : Nat) : Set where
  constructor half-shell-split
  field
    lowerSamples : List (LowerHalfSample outputShell)
    upperSamples : List (UpperHalfSample outputShell)

open HalfShellSplit public

splitAtHalf :
  (outputShell : Nat) →
  List IndexedShellValue →
  HalfShellSplit outputShell
splitAtHalf outputShell [] = half-shell-split [] []
splitAtHalf outputShell (sampleValue ∷ samples)
  with shellIndex sampleValue + shellIndex sampleValue ≤? outputShell
     | splitAtHalf outputShell samples
... | yes proof | half-shell-split lower upper =
  half-shell-split
    (lower-half-sample sampleValue proof ∷ lower)
    upper
... | no refutation | half-shell-split lower upper =
  half-shell-split
    lower
    (upper-half-sample sampleValue refutation ∷ upper)

sumOriginal : List IndexedShellValue → ℚ
sumOriginal [] = 0ℚ
sumOriginal (sampleValue ∷ samples) =
  amplitude sampleValue + sumOriginal samples

sumLower :
  ∀ {outputShell} →
  List (LowerHalfSample outputShell) → ℚ
sumLower [] = 0ℚ
sumLower (wrapped ∷ samples) =
  amplitude (lowerSample wrapped) + sumLower samples

sumUpper :
  ∀ {outputShell} →
  List (UpperHalfSample outputShell) → ℚ
sumUpper [] = 0ℚ
sumUpper (wrapped ∷ samples) =
  amplitude (upperSample wrapped) + sumUpper samples

halfSplitReconstructsFold :
  (outputShell : Nat) →
  (samples : List IndexedShellValue) →
  sumOriginal samples
  ≡ sumLower (lowerSamples (splitAtHalf outputShell samples))
    + sumUpper (upperSamples (splitAtHalf outputShell samples))
halfSplitReconstructsFold outputShell [] = solve []
halfSplitReconstructsFold outputShell (sampleValue ∷ samples)
  with shellIndex sampleValue + shellIndex sampleValue ≤? outputShell
     | splitAtHalf outputShell samples
     | halfSplitReconstructsFold outputShell samples
... | yes proof | half-shell-split lower upper | induction
  rewrite induction =
  solve
    ( amplitude sampleValue
    ∷ sumLower lower
    ∷ sumUpper upper
    ∷ []
    )
... | no refutation | half-shell-split lower upper | induction
  rewrite induction =
  solve
    ( amplitude sampleValue
    ∷ sumLower lower
    ∷ sumUpper upper
    ∷ []
    )

finiteHalfShellPartitionClosed : Bool
finiteHalfShellPartitionClosed = true

finiteHalfShellFoldReconstructionClosed : Bool
finiteHalfShellFoldReconstructionClosed = true

finiteHalfShellPartitionClosedIsTrue :
  finiteHalfShellPartitionClosed ≡ true
finiteHalfShellPartitionClosedIsTrue = refl

finiteHalfShellFoldReconstructionClosedIsTrue :
  finiteHalfShellFoldReconstructionClosed ≡ true
finiteHalfShellFoldReconstructionClosedIsTrue = refl
