module DASHI.Physics.Closure.NSTriadKNLuoFiniteMeanValueSelectionExact where

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
-- Prove the finite ordered analogue of Luo's mean-value selection in Section
-- 4.  Every nonempty rational time window has a selected sample which occurs
-- in the window, is below every other sample, and hence satisfies the exact
-- cross-multiplied average estimate
--
--   (# window) * selected <= sum window.
--
-- The minimum and its occurrence proof are constructed recursively from the
-- total order on rationals.  The average estimate is then proved by finite-sum
-- monotonicity.  No selected time or mean-value inequality is supplied as an
-- input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedIncrementFubiniExact as Finite

data Occurs (value : ℚ) : List ℚ → Set where
  here : ∀ {values} → Occurs value (value ∷ values)
  there : ∀ {head values} → Occurs value values → Occurs value (head ∷ values)

record SelectedMinimum (values : List ℚ) : Set where
  constructor selected-minimum
  field
    value : ℚ
    occurs : Occurs value values
    belowEvery :
      (candidate : ℚ) → Occurs candidate values → value ≤ candidate

open SelectedMinimum public

singletonMinimum :
  (head : ℚ) → SelectedMinimum (head ∷ [])
singletonMinimum head =
  selected-minimum
    head
    here
    (λ candidate occurrence → singletonOccurrence candidate occurrence)
  where
    singletonOccurrence :
      (candidate : ℚ) → Occurs candidate (head ∷ []) → head ≤ candidate
    singletonOccurrence candidate here = ℚₚ.≤-refl

prependMinimum :
  (head : ℚ) →
  ∀ {tail} →
  SelectedMinimum tail →
  SelectedMinimum (head ∷ tail)
prependMinimum head {tail} minimum
  with ℚₚ.≤-total head (value minimum)
... | inj₁ head≤minimum =
  selected-minimum
    head
    here
    below
  where
    below :
      (candidate : ℚ) →
      Occurs candidate (head ∷ tail) →
      head ≤ candidate
    below candidate here = ℚₚ.≤-refl
    below candidate (there occurrence) =
      ℚₚ.≤-trans
        head≤minimum
        (belowEvery minimum candidate occurrence)
... | inj₂ minimum≤head =
  selected-minimum
    (value minimum)
    (there (occurs minimum))
    below
  where
    below :
      (candidate : ℚ) →
      Occurs candidate (head ∷ tail) →
      value minimum ≤ candidate
    below candidate here = minimum≤head
    below candidate (there occurrence) =
      belowEvery minimum candidate occurrence

selectMinimum :
  (head : ℚ) →
  (tail : List ℚ) →
  SelectedMinimum (head ∷ tail)
selectMinimum head [] = singletonMinimum head
selectMinimum head (next ∷ rest) =
  prependMinimum head (selectMinimum next rest)

listLength : List ℚ → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

natScale : Nat → ℚ → ℚ
natScale zero value = 0ℚ
natScale (suc count) value = value + natScale count value

sumValues : List ℚ → ℚ
sumValues values = Finite.sumList values (λ value → value)

lowerBoundScalesBelowSum :
  (lower : ℚ) →
  (values : List ℚ) →
  ((candidate : ℚ) → Occurs candidate values → lower ≤ candidate) →
  natScale (listLength values) lower ≤ sumValues values
lowerBoundScalesBelowSum lower [] lowerBound = ℚₚ.≤-refl
lowerBoundScalesBelowSum lower (head ∷ values) lowerBound =
  ℚₚ.+-mono-≤
    (lowerBound head here)
    (lowerBoundScalesBelowSum
      lower
      values
      (λ candidate occurrence → lowerBound candidate (there occurrence)))

record FiniteMeanValueSelection (values : List ℚ) : Set where
  constructor finite-mean-value
  field
    selected : ℚ
    selectedOccurs : Occurs selected values
    selectedBelowEvery :
      (candidate : ℚ) → Occurs candidate values → selected ≤ candidate
    crossMultipliedAverageBound :
      natScale (listLength values) selected ≤ sumValues values

open FiniteMeanValueSelection public

finiteMeanValueSelection :
  (head : ℚ) →
  (tail : List ℚ) →
  FiniteMeanValueSelection (head ∷ tail)
finiteMeanValueSelection head tail =
  let minimum = selectMinimum head tail
  in
  finite-mean-value
    (value minimum)
    (occurs minimum)
    (belowEvery minimum)
    (lowerBoundScalesBelowSum
      (value minimum)
      (head ∷ tail)
      (belowEvery minimum))

finiteMeanValueSelectionConstructed : Bool
finiteMeanValueSelectionConstructed = true

finiteCrossMultipliedAverageBoundClosed : Bool
finiteCrossMultipliedAverageBoundClosed = true

finiteMeanValueSelectionConstructedIsTrue :
  finiteMeanValueSelectionConstructed ≡ true
finiteMeanValueSelectionConstructedIsTrue = refl

finiteCrossMultipliedAverageBoundClosedIsTrue :
  finiteCrossMultipliedAverageBoundClosed ≡ true
finiteCrossMultipliedAverageBoundClosedIsTrue = refl
