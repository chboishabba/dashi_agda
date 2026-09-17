module DASHI.Biology.Agriculture.SevenGenerationBNFBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- THIN SEVEN-GENERATION BNF PLANNING BOUNDARY
--
-- This module is intentionally self-contained and dependency-light.
-- It records the planning boundary flags without importing the heavy
-- climate, deep-time prebiotic chemistry, or physics closures.
------------------------------------------------------------------------

record SevenGenerationBNFBoundary : Set where
  constructor seven-generation-bnf-boundary
  field
    presentProfitDeterminesGenerationSevenOptions : Bool
    presentProfitDeterminesGenerationSevenOptionsIsFalse : presentProfitDeterminesGenerationSevenOptions ≡ false
    everyIntermediateGenerationMustBeCollapsedIntoTerminalValue : Bool
    everyIntermediateGenerationMustBeCollapsedIntoTerminalValueIsFalse : everyIntermediateGenerationMustBeCollapsedIntoTerminalValue ≡ false
    CountryAuthorityIsIndependentLongHorizonCoordinate : Bool
    CountryAuthorityIsIndependentLongHorizonCoordinateIsTrue : CountryAuthorityIsIndependentLongHorizonCoordinate ≡ true
    longHorizonProducerSchedulingIsConsumerRelative : Bool
    longHorizonProducerSchedulingIsConsumerRelativeIsTrue : longHorizonProducerSchedulingIsConsumerRelative ≡ true

open SevenGenerationBNFBoundary public

canonicalSevenGenerationBNFBoundary : SevenGenerationBNFBoundary
canonicalSevenGenerationBNFBoundary =
  seven-generation-bnf-boundary false refl false refl true refl true refl
