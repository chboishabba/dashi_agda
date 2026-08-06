module DASHI.Physics.Closure.NSTriadKNLuoFiniteJ11HalfBudgetExact where

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
-- Preserve the source's two different controls on the r<=q/2 and r>q/2
-- portions of J11.  Each evidence-carrying half-shell sample receives its own
-- pointwise square budget.  Finite summation proves the two aggregate square
-- budgets, and the indexed source theorem then derives the complete J11
-- estimate.  Lower and upper budgets are never conflated into one pointwise
-- multiplier hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHalfShellPartitionExact as Partition
import DASHI.Physics.Closure.NSTriadKNLuoFiniteIndexedSourceSection4Exact as Indexed

sumLowerBudget :
  ∀ {outputShell} →
  (Partition.LowerHalfSample outputShell → ℚ) →
  List (Partition.LowerHalfSample outputShell) → ℚ
sumLowerBudget budget [] = 0ℚ
sumLowerBudget budget (wrapped ∷ rest) =
  budget wrapped + sumLowerBudget budget rest

sumUpperBudget :
  ∀ {outputShell} →
  (Partition.UpperHalfSample outputShell → ℚ) →
  List (Partition.UpperHalfSample outputShell) → ℚ
sumUpperBudget budget [] = 0ℚ
sumUpperBudget budget (wrapped ∷ rest) =
  budget wrapped + sumUpperBudget budget rest

lowerSquaresBelowBudget :
  ∀ {outputShell}
    (budget : Partition.LowerHalfSample outputShell → ℚ)
    (samples : List (Partition.LowerHalfSample outputShell)) →
  ((wrapped : Partition.LowerHalfSample outputShell) →
    L2.square (Partition.amplitude (Partition.lowerSample wrapped))
    ≤ budget wrapped) →
  Jensen.sumSquares (Indexed.lowerValues samples)
  ≤ sumLowerBudget budget samples
lowerSquaresBelowBudget budget [] pointwise = ℚₚ.≤-refl
lowerSquaresBelowBudget budget (wrapped ∷ rest) pointwise =
  ℚₚ.+-mono-≤
    (pointwise wrapped)
    (lowerSquaresBelowBudget budget rest pointwise)

upperSquaresBelowBudget :
  ∀ {outputShell}
    (budget : Partition.UpperHalfSample outputShell → ℚ)
    (samples : List (Partition.UpperHalfSample outputShell)) →
  ((wrapped : Partition.UpperHalfSample outputShell) →
    L2.square (Partition.amplitude (Partition.upperSample wrapped))
    ≤ budget wrapped) →
  Jensen.sumSquares (Indexed.upperValues samples)
  ≤ sumUpperBudget budget samples
upperSquaresBelowBudget budget [] pointwise = ℚₚ.≤-refl
upperSquaresBelowBudget budget (wrapped ∷ rest) pointwise =
  ℚₚ.+-mono-≤
    (pointwise wrapped)
    (upperSquaresBelowBudget budget rest pointwise)

record J11HalfBudgetData : Set where
  constructor j11-half-budget
  field
    outputShell : Nat
    indexedSamples : List Partition.IndexedShellValue

    lowerBudget :
      Partition.LowerHalfSample outputShell → ℚ
    upperBudget :
      Partition.UpperHalfSample outputShell → ℚ

    lowerPointwiseBound :
      (wrapped : Partition.LowerHalfSample outputShell) →
      L2.square (Partition.amplitude (Partition.lowerSample wrapped))
      ≤ lowerBudget wrapped

    upperPointwiseBound :
      (wrapped : Partition.UpperHalfSample outputShell) →
      L2.square (Partition.amplitude (Partition.upperSample wrapped))
      ≤ upperBudget wrapped

open J11HalfBudgetData public

split :
  (data : J11HalfBudgetData) →
  Partition.HalfShellSplit (outputShell data)
split data =
  Partition.splitAtHalf (outputShell data) (indexedSamples data)

lowerBudgetTotal : J11HalfBudgetData → ℚ
lowerBudgetTotal data =
  sumLowerBudget (lowerBudget data)
    (Partition.lowerSamples (split data))

upperBudgetTotal : J11HalfBudgetData → ℚ
upperBudgetTotal data =
  sumUpperBudget (upperBudget data)
    (Partition.upperSamples (split data))

lowerHalfSquareBudget :
  (data : J11HalfBudgetData) →
  Jensen.sumSquares
    (Indexed.lowerValues (Partition.lowerSamples (split data)))
  ≤ lowerBudgetTotal data
lowerHalfSquareBudget data =
  lowerSquaresBelowBudget
    (lowerBudget data)
    (Partition.lowerSamples (split data))
    (lowerPointwiseBound data)

upperHalfSquareBudget :
  (data : J11HalfBudgetData) →
  Jensen.sumSquares
    (Indexed.upperValues (Partition.upperSamples (split data)))
  ≤ upperBudgetTotal data
upperHalfSquareBudget data =
  upperSquaresBelowBudget
    (upperBudget data)
    (Partition.upperSamples (split data))
    (upperPointwiseBound data)

asIndexedSourceData :
  (data : J11HalfBudgetData) →
  (j12Samples j2Samples : List ℚ) →
  (j12Energy j2Energy : ℚ) →
  Jensen.sumSquares j12Samples ≤ j12Energy →
  Jensen.sumSquares j2Samples ≤ j2Energy →
  Indexed.IndexedSourceSection4Data
asIndexedSourceData data j12Samples j2Samples j12Energy j2Energy
  j12Bound j2Bound =
  Indexed.indexed-source-section4
    (outputShell data)
    (indexedSamples data)
    j12Samples
    j2Samples
    (lowerBudgetTotal data)
    (upperBudgetTotal data)
    j12Energy
    j2Energy
    (lowerHalfSquareBudget data)
    (upperHalfSquareBudget data)
    j12Bound
    j2Bound

j11HalfBudgetBound :
  (data : J11HalfBudgetData) →
  L2.square (Partition.sumOriginal (indexedSamples data))
  ≤ Half.two
    * ( Jensen.rationalLength
          (Indexed.lowerValues (Partition.lowerSamples (split data)))
        * lowerBudgetTotal data
      + Jensen.rationalLength
          (Indexed.upperValues (Partition.upperSamples (split data)))
        * upperBudgetTotal data)
j11HalfBudgetBound data =
  let
    sourceData =
      asIndexedSourceData data [] [] 0ℚ 0ℚ
        ℚₚ.≤-refl ℚₚ.≤-refl
  in
  Indexed.indexedJ11SourceBound sourceData

finiteJ11SeparateHalfBudgetsClosed : Bool
finiteJ11SeparateHalfBudgetsClosed = true

finiteJ11SeparateHalfBudgetsClosedIsTrue :
  finiteJ11SeparateHalfBudgetsClosed ≡ true
finiteJ11SeparateHalfBudgetsClosedIsTrue = refl
