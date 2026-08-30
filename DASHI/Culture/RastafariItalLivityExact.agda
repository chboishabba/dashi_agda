module DASHI.Culture.RastafariItalLivityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RASTAFARI ITAL LIVITY — SOURCE-BOUNDED CULTURAL OWNER
--
-- External calibration:
-- Joseph Powell, "Ital Hermeneutics: The Innovative Theological Grounding of
-- Rastafari Dietary (Ietary) Practices", Black Theology 19(1), 2021, 32--52.
-- DOI: 10.1080/14769948.2021.1897097
------------------------------------------------------------------------

data ItalDimension : Set where
  food body land community materialPractice spirituality : ItalDimension

data PracticeQuality : Set where
  lifePromoting natural minimallyAdulterated locallyProduced communal : PracticeQuality

data FoodPractice : Set where
  plantFood localFood organicFood processedFood tinnedFood animalFood addedSalt artificialAdditive : FoodPractice

data LivityStrength : Set where
  associatedPractice strictItal : LivityStrength

record ItalLivityProfile : Set where
  constructor italLivityProfile
  field
    dimension : ItalDimension → Set
    quality : PracticeQuality → Set
    foodPractice : FoodPractice → Set
    strength : LivityStrength

open ItalLivityProfile public

canonicalItalProfile : ItalLivityProfile
canonicalItalProfile =
  italLivityProfile
    canonicalDimension
    canonicalQuality
    canonicalFoodPractice
    associatedPractice
  where
    canonicalDimension : ItalDimension → Set
    canonicalDimension food = ⊤
    canonicalDimension body = ⊤
    canonicalDimension land = ⊤
    canonicalDimension community = ⊤
    canonicalDimension materialPractice = ⊤
    canonicalDimension spirituality = ⊤

    canonicalQuality : PracticeQuality → Set
    canonicalQuality lifePromoting = ⊤
    canonicalQuality natural = ⊤
    canonicalQuality minimallyAdulterated = ⊤
    canonicalQuality locallyProduced = ⊤
    canonicalQuality communal = ⊤

    canonicalFoodPractice : FoodPractice → Set
    canonicalFoodPractice plantFood = ⊤
    canonicalFoodPractice localFood = ⊤
    canonicalFoodPractice organicFood = ⊤
    canonicalFoodPractice processedFood = ⊥
    canonicalFoodPractice tinnedFood = ⊥
    canonicalFoodPractice animalFood = ⊥
    canonicalFoodPractice addedSalt = ⊥
    canonicalFoodPractice artificialAdditive = ⊥

canonicalItalIsMoreThanDiet :
  dimension canonicalItalProfile food ×
  (dimension canonicalItalProfile land ×
   dimension canonicalItalProfile community)
canonicalItalIsMoreThanDiet = tt , (tt , tt)

canonicalItalValuesLifeAndNaturalness :
  quality canonicalItalProfile lifePromoting ×
  quality canonicalItalProfile natural
canonicalItalValuesLifeAndNaturalness = tt , tt

data ItalIsIdenticalToPermaculture : Set where

data ItalIsIdenticalToVeganism : Set where

data EveryRastafariPracticeIsStrictItal : Set where

italIsNotAutoIdentifiedWithPermaculture : ItalIsIdenticalToPermaculture → ⊥
italIsNotAutoIdentifiedWithPermaculture ()

italIsNotAutoIdentifiedWithVeganism : ItalIsIdenticalToVeganism → ⊥
italIsNotAutoIdentifiedWithVeganism ()

practiceVariationBlocksUniversalStrictness : EveryRastafariPracticeIsStrictItal → ⊥
practiceVariationBlocksUniversalStrictness ()

record ItalAttributionBoundary : Set where
  constructor italAttributionBoundary
  field
    sourceClaimsDASHIPlanningTheorems : Bool
    sourceClaimsDASHIPlanningTheoremsIsFalse : sourceClaimsDASHIPlanningTheorems ≡ false

    sourceClaimsPermacultureIdentity : Bool
    sourceClaimsPermacultureIdentityIsFalse : sourceClaimsPermacultureIdentity ≡ false

    sourceSupportsLifeValuation : Bool
    sourceSupportsLifeValuationIsTrue : sourceSupportsLifeValuation ≡ true

    sourceSupportsPracticeVariation : Bool
    sourceSupportsPracticeVariationIsTrue : sourceSupportsPracticeVariation ≡ true

canonicalItalAttributionBoundary : ItalAttributionBoundary
canonicalItalAttributionBoundary =
  italAttributionBoundary
    false refl
    false refl
    true refl
    true refl
