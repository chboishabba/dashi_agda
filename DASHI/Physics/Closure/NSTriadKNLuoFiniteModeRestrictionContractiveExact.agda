module DASHI.Physics.Closure.NSTriadKNLuoFiniteModeRestrictionContractiveExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- State the finite support projection theorem on actual mode-indexed
-- coefficient squares.  Filtering by an arbitrary Boolean predicate on the
-- mode cannot increase the sum of nonnegative coefficient squares. Therefore
-- Parseval gives
--
--   ||P_Lambda f||_2^2 <= ||f||_2^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

record ModeCoefficientSquare (Mode : Set) : Set where
  constructor mode-coefficient-square
  field
    mode : Mode
    coefficientSquared : ℚ
    coefficientSquaredNonnegative : 0ℚ ≤ coefficientSquared

open ModeCoefficientSquare public

sumCoefficientSquares :
  ∀ {Mode : Set} →
  List (ModeCoefficientSquare Mode) → ℚ
sumCoefficientSquares [] = 0ℚ
sumCoefficientSquares (item ∷ items) =
  coefficientSquared item + sumCoefficientSquares items

filterModes :
  ∀ {Mode : Set} →
  (Mode → Bool) →
  List (ModeCoefficientSquare Mode) →
  List (ModeCoefficientSquare Mode)
filterModes predicate [] = []
filterModes predicate (item ∷ items) with predicate (mode item)
... | true = item ∷ filterModes predicate items
... | false = filterModes predicate items

filteredModeEnergyBelowFull :
  ∀ {Mode : Set}
    (predicate : Mode → Bool)
    (items : List (ModeCoefficientSquare Mode)) →
  sumCoefficientSquares (filterModes predicate items)
  ≤ sumCoefficientSquares items
filteredModeEnergyBelowFull predicate [] = ℚₚ.≤-refl
filteredModeEnergyBelowFull predicate (item ∷ items)
  with predicate (mode item)
... | true =
  ℚₚ.+-mono-≤
    ℚₚ.≤-refl
    (filteredModeEnergyBelowFull predicate items)
... | false =
  let
    tailBound = filteredModeEnergyBelowFull predicate items

    tailBelowWhole :
      sumCoefficientSquares items
      ≤ coefficientSquared item + sumCoefficientSquares items
    tailBelowWhole =
      subst
        (λ lower →
          lower ≤ coefficientSquared item + sumCoefficientSquares items)
        (ℚₚ.+-identityˡ (sumCoefficientSquares items))
        (ℚₚ.+-mono-≤
          (coefficientSquaredNonnegative item)
          ℚₚ.≤-refl)
  in
  ℚₚ.≤-trans tailBound tailBelowWhole

record FiniteModeRestrictionData (Mode : Set) : Set₁ where
  constructor finite-mode-restriction-data
  field
    physicalL2Squared : ℚ
    coefficients : List (ModeCoefficientSquare Mode)
    supportPredicate : Mode → Bool
    parsevalMeaning :
      physicalL2Squared ≡ sumCoefficientSquares coefficients

open FiniteModeRestrictionData public

restrictedL2Squared :
  ∀ {Mode : Set} →
  FiniteModeRestrictionData Mode → ℚ
restrictedL2Squared dataSet =
  sumCoefficientSquares
    (filterModes
      (supportPredicate dataSet)
      (coefficients dataSet))

finiteModeRestrictionContractive :
  ∀ {Mode : Set}
    (dataSet : FiniteModeRestrictionData Mode) →
  restrictedL2Squared dataSet ≤ physicalL2Squared dataSet
finiteModeRestrictionContractive dataSet =
  subst
    (λ upper → restrictedL2Squared dataSet ≤ upper)
    (sym (parsevalMeaning dataSet))
    (filteredModeEnergyBelowFull
      (supportPredicate dataSet)
      (coefficients dataSet))
