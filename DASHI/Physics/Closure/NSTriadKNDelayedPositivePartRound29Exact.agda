module DASHI.Physics.Closure.NSTriadKNDelayedPositivePartRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- DASHI CONTRIBUTION
--
-- Positive taxation is delayed until every signed constituent in one owner
-- fibre has been summed. The atomwise positive-part or absolute-value route is
-- exposed only as a named lossy fallback.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

signedSum : List ℚ → ℚ
signedSum [] = 0ℚ
signedSum (value ∷ rest) = value + signedSum rest

atomwiseMagnitude : List ℚ → ℚ
atomwiseMagnitude [] = 0ℚ
atomwiseMagnitude (value ∷ rest) = ∣ value ∣ + atomwiseMagnitude rest

delayedMagnitudeBelowAtomwiseMagnitude :
  (values : List ℚ) →
  ∣ signedSum values ∣ ≤ atomwiseMagnitude values
delayedMagnitudeBelowAtomwiseMagnitude [] =
  subst
    (λ value → value ≤ 0ℚ)
    (sym (ℚₚ.0≤p⇒∣p∣≡p ℚₚ.≤-refl))
    ℚₚ.≤-refl
delayedMagnitudeBelowAtomwiseMagnitude (value ∷ rest) =
  ℚₚ.≤-trans
    (ℚₚ.∣p+q∣≤∣p∣+∣q∣ value (signedSum rest))
    (ℚₚ.+-mono-≤
      ℚₚ.≤-refl
      (delayedMagnitudeBelowAtomwiseMagnitude rest))

oppositePairCancelsBeforeMagnitude :
  (value : ℚ) →
  signedSum (value ∷ (0ℚ - value) ∷ []) ≡ 0ℚ
oppositePairCancelsBeforeMagnitude value = solve (value ∷ [])

record PositivePartLaws : Set₁ where
  field
    positivePart : ℚ → ℚ
    positiveZero : positivePart 0ℚ ≡ 0ℚ
    positiveSubadditive : ∀ left right →
      positivePart (left + right)
      ≤ positivePart left + positivePart right

open PositivePartLaws public

sumPositiveParts : PositivePartLaws → List ℚ → ℚ
sumPositiveParts laws [] = 0ℚ
sumPositiveParts laws (value ∷ rest) =
  positivePart laws value + sumPositiveParts laws rest

delayedPositivePartBelowAtomwiseFallback :
  (laws : PositivePartLaws) →
  (values : List ℚ) →
  positivePart laws (signedSum values)
  ≤ sumPositiveParts laws values
delayedPositivePartBelowAtomwiseFallback laws [] =
  subst
    (λ left → left ≤ 0ℚ)
    (positiveZero laws)
    ℚₚ.≤-refl
delayedPositivePartBelowAtomwiseFallback laws (value ∷ rest) =
  ℚₚ.≤-trans
    (positiveSubadditive laws value (signedSum rest))
    (ℚₚ.+-mono-≤
      ℚₚ.≤-refl
      (delayedPositivePartBelowAtomwiseFallback laws rest))

record DelayedOwnerTax (laws : PositivePartLaws) : Set where
  constructor delayed-owner-tax
  field
    signedConstituents : List ℚ
    groupedSignedValue : ℚ
    groupedValueMeaning : groupedSignedValue ≡ signedSum signedConstituents

open DelayedOwnerTax public

groupedPositiveTax :
  (laws : PositivePartLaws) → DelayedOwnerTax laws → ℚ
groupedPositiveTax laws tax = positivePart laws (groupedSignedValue tax)

atomwisePositiveFallback :
  (laws : PositivePartLaws) → DelayedOwnerTax laws → ℚ
atomwisePositiveFallback laws tax =
  sumPositiveParts laws (signedConstituents tax)

groupedTaxBelowLossyFallback :
  (laws : PositivePartLaws) →
  (tax : DelayedOwnerTax laws) →
  groupedPositiveTax laws tax ≤ atomwisePositiveFallback laws tax
groupedTaxBelowLossyFallback laws tax =
  subst
    (λ grouped →
      positivePart laws grouped
      ≤ atomwisePositiveFallback laws tax)
    (sym (groupedValueMeaning tax))
    (delayedPositivePartBelowAtomwiseFallback laws
      (signedConstituents tax))

delayedPositivePartArchitectureClosed : Bool
delayedPositivePartArchitectureClosed = true

delayedPositivePartArchitectureClosedIsTrue :
  delayedPositivePartArchitectureClosed ≡ true
delayedPositivePartArchitectureClosedIsTrue = refl
