module DASHI.Physics.Closure.NSTriadKNLuoFiniteHalfShellEnergyPartitionExact where

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
-- Strengthen the literal 2r<=q / 2r>q partition from amplitude reconstruction
-- to energy reconstruction.  The complete sum of squared amplitudes is proved
-- to equal the lower-half square fold plus the upper-half square fold.  This
-- is the exact finite bookkeeping needed before the two ranges receive
-- different energy and dissipation estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHalfShellPartitionExact as Partition

squareOriginal : List Partition.IndexedShellValue → ℚ
squareOriginal [] = 0ℚ
squareOriginal (sampleValue ∷ samples) =
  L2.square (Partition.amplitude sampleValue) + squareOriginal samples

squareLower :
  ∀ {outputShell} →
  List (Partition.LowerHalfSample outputShell) → ℚ
squareLower [] = 0ℚ
squareLower (wrapped ∷ samples) =
  L2.square (Partition.amplitude (Partition.lowerSample wrapped))
  + squareLower samples

squareUpper :
  ∀ {outputShell} →
  List (Partition.UpperHalfSample outputShell) → ℚ
squareUpper [] = 0ℚ
squareUpper (wrapped ∷ samples) =
  L2.square (Partition.amplitude (Partition.upperSample wrapped))
  + squareUpper samples

halfSplitReconstructsSquareFold :
  (outputShell : Nat) →
  (samples : List Partition.IndexedShellValue) →
  squareOriginal samples
  ≡ squareLower
      (Partition.lowerSamples (Partition.splitAtHalf outputShell samples))
    + squareUpper
      (Partition.upperSamples (Partition.splitAtHalf outputShell samples))
halfSplitReconstructsSquareFold outputShell [] = solve []
halfSplitReconstructsSquareFold outputShell (sampleValue ∷ samples)
  with Partition.shellIndex sampleValue + Partition.shellIndex sampleValue
       ≤? outputShell
     | Partition.splitAtHalf outputShell samples
     | halfSplitReconstructsSquareFold outputShell samples
... | yes proof | Partition.half-shell-split lower upper | induction
  rewrite induction =
  solve
    ( L2.square (Partition.amplitude sampleValue)
    ∷ squareLower lower
    ∷ squareUpper upper
    ∷ []
    )
... | no refutation | Partition.half-shell-split lower upper | induction
  rewrite induction =
  solve
    ( L2.square (Partition.amplitude sampleValue)
    ∷ squareLower lower
    ∷ squareUpper upper
    ∷ []
    )

squareOriginalNonnegative :
  (samples : List Partition.IndexedShellValue) →
  0ℚ ≤ squareOriginal samples
squareOriginalNonnegative [] = ℚₚ.≤-refl
squareOriginalNonnegative (sampleValue ∷ samples) =
  L2.addNonnegative
    (L2.squareNonnegative (Partition.amplitude sampleValue))
    (squareOriginalNonnegative samples)

squareLowerNonnegative :
  ∀ {outputShell}
    (samples : List (Partition.LowerHalfSample outputShell)) →
  0ℚ ≤ squareLower samples
squareLowerNonnegative [] = ℚₚ.≤-refl
squareLowerNonnegative (wrapped ∷ samples) =
  L2.addNonnegative
    (L2.squareNonnegative
      (Partition.amplitude (Partition.lowerSample wrapped)))
    (squareLowerNonnegative samples)

squareUpperNonnegative :
  ∀ {outputShell}
    (samples : List (Partition.UpperHalfSample outputShell)) →
  0ℚ ≤ squareUpper samples
squareUpperNonnegative [] = ℚₚ.≤-refl
squareUpperNonnegative (wrapped ∷ samples) =
  L2.addNonnegative
    (L2.squareNonnegative
      (Partition.amplitude (Partition.upperSample wrapped)))
    (squareUpperNonnegative samples)

finiteHalfShellEnergyPartitionClosed : Bool
finiteHalfShellEnergyPartitionClosed = true

finiteHalfShellEnergyPartitionClosedIsTrue :
  finiteHalfShellEnergyPartitionClosed ≡ true
finiteHalfShellEnergyPartitionClosedIsTrue = refl
