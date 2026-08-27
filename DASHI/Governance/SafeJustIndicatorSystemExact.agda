module DASHI.Governance.SafeJustIndicatorSystemExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- O'NEILL ET AL. 2018 INDICATOR GEOMETRY
--
-- Seven biophysical and eleven social coordinates are kept as typed vectors.
-- Count summaries are lossy observers of those vectors, not substitutes for
-- the underlying coordinate state.
------------------------------------------------------------------------

data BiophysicalIndicator : Set where
  co2Emissions phosphorus nitrogen blueWater eHANPP ecologicalFootprint materialFootprint : BiophysicalIndicator

data SocialRole : Set where
  needSatisfier wellbeingMeasure : SocialRole

data SocialIndicator : Set where
  nutrition sanitation income energyAccess education socialSupport democraticQuality equality employment lifeSatisfaction healthyLifeExpectancy : SocialIndicator

socialRole : SocialIndicator → SocialRole
socialRole lifeSatisfaction = wellbeingMeasure
socialRole healthyLifeExpectancy = wellbeingMeasure
socialRole _ = needSatisfier

record BiophysicalProfile : Set where
  constructor biophysicalProfile
  field
    co2Over phosphorusOver nitrogenOver blueWaterOver eHANPPOver ecologicalFootprintOver materialFootprintOver : Bool

open BiophysicalProfile public

record SocialProfile : Set where
  constructor socialProfile
  field
    nutritionMet sanitationMet incomeMet energyAccessMet educationMet socialSupportMet democraticQualityMet equalityMet employmentMet lifeSatisfactionMet healthyLifeExpectancyMet : Bool

open SocialProfile public

boolToNat : Bool → Nat
boolToNat false = 0
boolToNat true = 1

bioTransgressionCount : BiophysicalProfile → Nat
bioTransgressionCount p =
  boolToNat (co2Over p) +
  boolToNat (phosphorusOver p) +
  boolToNat (nitrogenOver p) +
  boolToNat (blueWaterOver p) +
  boolToNat (eHANPPOver p) +
  boolToNat (ecologicalFootprintOver p) +
  boolToNat (materialFootprintOver p)

socialThresholdCount : SocialProfile → Nat
socialThresholdCount p =
  boolToNat (nutritionMet p) +
  boolToNat (sanitationMet p) +
  boolToNat (incomeMet p) +
  boolToNat (energyAccessMet p) +
  boolToNat (educationMet p) +
  boolToNat (socialSupportMet p) +
  boolToNat (democraticQualityMet p) +
  boolToNat (equalityMet p) +
  boolToNat (employmentMet p) +
  boolToNat (lifeSatisfactionMet p) +
  boolToNat (healthyLifeExpectancyMet p)

------------------------------------------------------------------------
-- Safe-and-just status is conjunctive.  It is not another scalar indicator.
------------------------------------------------------------------------

allBioWithin : BiophysicalProfile → Bool
allBioWithin (biophysicalProfile false false false false false false false) = true
allBioWithin _ = false

allSocialMet : SocialProfile → Bool
allSocialMet (socialProfile true true true true true true true true true true true) = true
allSocialMet _ = false

record CountryObservation : Set where
  constructor countryObservation
  field
    biophysical : BiophysicalProfile
    social : SocialProfile

open CountryObservation public

safeAndJust : CountryObservation → Bool
safeAndJust c with allBioWithin (biophysical c) | allSocialMet (social c)
... | true | true = true
... | _ | _ = false

------------------------------------------------------------------------
-- Exact finite witnesses that the count projections erase coordinates.
------------------------------------------------------------------------

bioA bioB : BiophysicalProfile
bioA = biophysicalProfile true false false false false false false
bioB = biophysicalProfile false true false false false false false

sameBioCount : bioTransgressionCount bioA ≡ bioTransgressionCount bioB
sameBioCount = refl

sameBioCountDoesNotRecoverCO2 : co2Over bioA ≡ co2Over bioB → ⊥
sameBioCountDoesNotRecoverCO2 ()

socialA socialB : SocialProfile
socialA = socialProfile true false false false false false false false false false false
socialB = socialProfile false true false false false false false false false false false

sameSocialCount : socialThresholdCount socialA ≡ socialThresholdCount socialB
sameSocialCount = refl

sameSocialCountDoesNotRecoverNutrition : nutritionMet socialA ≡ nutritionMet socialB → ⊥
sameSocialCountDoesNotRecoverNutrition ()

record CountProjectionBoundary : Set where
  constructor countProjectionBoundary
  field
    equalBioCountImpliesEqualBioVector : Bool
    equalBioCountImpliesEqualBioVectorIsFalse : equalBioCountImpliesEqualBioVector ≡ false
    equalSocialCountImpliesEqualSocialVector : Bool
    equalSocialCountImpliesEqualSocialVectorIsFalse : equalSocialCountImpliesEqualSocialVector ≡ false
    safeAndJustIsIntersectionOfEcologicalAndSocialConditions : Bool
    safeAndJustIsIntersectionOfEcologicalAndSocialConditionsIsTrue :
      safeAndJustIsIntersectionOfEcologicalAndSocialConditions ≡ true

canonicalCountProjectionBoundary : CountProjectionBoundary
canonicalCountProjectionBoundary = countProjectionBoundary false refl false refl true refl
