module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierRestrictionContractiveExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Prove the support-restriction consequence of finite Parseval independently
-- of the character constructor.  A finite Fourier energy is represented by a
-- list of nonnegative coefficient squares. Filtering by any Boolean support
-- predicate can only decrease their sum. Therefore, once physical energy is
-- identified with the complete coefficient sum,
--
--   ||P_Lambda f||_2^2 <= ||f||_2^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

sum : List ℚ → ℚ
sum [] = 0ℚ
sum (value ∷ values) = value + sum values

filterBool : (ℚ → Bool) → List ℚ → List ℚ
filterBool predicate [] = []
filterBool predicate (value ∷ values) with predicate value
... | true = value ∷ filterBool predicate values
... | false = filterBool predicate values

data NonnegativeList : List ℚ → Set where
  nn[] : NonnegativeList []
  nn∷ :
    ∀ {value values} →
    0ℚ ≤ value →
    NonnegativeList values →
    NonnegativeList (value ∷ values)

filteredSumBelowFullSum :
  (predicate : ℚ → Bool) →
  (values : List ℚ) →
  NonnegativeList values →
  sum (filterBool predicate values) ≤ sum values
filteredSumBelowFullSum predicate [] nn[] = ℚₚ.≤-refl
filteredSumBelowFullSum predicate (value ∷ values) (nn∷ valueNN valuesNN)
  with predicate value
... | true =
  ℚₚ.+-mono-≤
    ℚₚ.≤-refl
    (filteredSumBelowFullSum predicate values valuesNN)
... | false =
  let
    tailBound = filteredSumBelowFullSum predicate values valuesNN

    tailBelowWhole :
      sum values ≤ value + sum values
    tailBelowWhole =
      subst
        (λ lower → lower ≤ value + sum values)
        (ℚₚ.+-identityˡ (sum values))
        (ℚₚ.+-mono-≤ valueNN ℚₚ.≤-refl)
  in
  ℚₚ.≤-trans tailBound tailBelowWhole

record FiniteFourierRestrictionData : Set where
  constructor finite-fourier-restriction-data
  field
    physicalL2Squared : ℚ
    coefficientSquares : List ℚ
    coefficientSquaresNonnegative : NonnegativeList coefficientSquares
    supportPredicate : ℚ → Bool
    parsevalMeaning : physicalL2Squared ≡ sum coefficientSquares

open FiniteFourierRestrictionData public

restrictedFourierL2Squared : FiniteFourierRestrictionData → ℚ
restrictedFourierL2Squared dataSet =
  sum (filterBool
    (supportPredicate dataSet)
    (coefficientSquares dataSet))

finiteFourierRestrictionContractive :
  (dataSet : FiniteFourierRestrictionData) →
  restrictedFourierL2Squared dataSet ≤ physicalL2Squared dataSet
finiteFourierRestrictionContractive dataSet =
  subst
    (λ upper → restrictedFourierL2Squared dataSet ≤ upper)
    (sym (parsevalMeaning dataSet))
    (filteredSumBelowFullSum
      (supportPredicate dataSet)
      (coefficientSquares dataSet)
      (coefficientSquaresNonnegative dataSet))
