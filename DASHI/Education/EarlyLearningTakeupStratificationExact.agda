module DASHI.Education.EarlyLearningTakeupStratificationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningIntersectionalCapabilityExact as Capability

------------------------------------------------------------------------
-- FORMAL AVAILABILITY != UPTAKE DISTRIBUTION
--
-- Nordic cash-for-care evidence motivates keeping uptake and labour incidence
-- as separate situated coordinates.  Equal legal availability of an option does
-- not imply equal uptake across household positions, nor equal labour effects.
-- The finite witness is structural; it is not an individual-level prediction.
------------------------------------------------------------------------

data CashCareAvailability : Set where
  sameCashCareOption : CashCareAvailability

data UptakePosition : Set where
  lowerObservedUptakePosition higherObservedUptakePosition : UptakePosition

data UptakeLevel : Set where
  lowerUptake higherUptake : UptakeLevel

data LabourIncidence : Set where
  lowerExitPressure higherExitPressure : LabourIncidence

availabilityProjection : UptakePosition → CashCareAvailability
availabilityProjection lowerObservedUptakePosition = sameCashCareOption
availabilityProjection higherObservedUptakePosition = sameCashCareOption

uptakeAt : UptakePosition → UptakeLevel
uptakeAt lowerObservedUptakePosition = lowerUptake
uptakeAt higherObservedUptakePosition = higherUptake

labourIncidenceAt : UptakePosition → LabourIncidence
labourIncidenceAt lowerObservedUptakePosition = lowerExitPressure
labourIncidenceAt higherObservedUptakePosition = higherExitPressure

uptakeDiffersAtSameAvailability :
  uptakeAt lowerObservedUptakePosition ≡
  uptakeAt higherObservedUptakePosition → ⊥
uptakeDiffersAtSameAvailability ()

labourIncidenceDiffersAtSameAvailability :
  labourIncidenceAt lowerObservedUptakePosition ≡
  labourIncidenceAt higherObservedUptakePosition → ⊥
labourIncidenceDiffersAtSameAvailability ()

availabilityCannotDetermineUptake :
  Intersection.FactorsThrough availabilityProjection uptakeAt → ⊥
availabilityCannotDetermineUptake =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      lowerObservedUptakePosition
      higherObservedUptakePosition
      refl
      uptakeDiffersAtSameAvailability)

availabilityCannotDetermineLabourIncidence :
  Intersection.FactorsThrough availabilityProjection labourIncidenceAt → ⊥
availabilityCannotDetermineLabourIncidence =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      lowerObservedUptakePosition
      higherObservedUptakePosition
      refl
      labourIncidenceDiffersAtSameAvailability)

------------------------------------------------------------------------
-- The existing intersectional carrier already retains labour position and
-- gendered care burden independently.  This module does not add a demographic
-- routing function; it only states that uptake/effect auditing must remain
-- stratified rather than being read from nominal availability.
------------------------------------------------------------------------

sameFamilyChoiceStillCannotDetermineCapability :
  Intersection.FactorsThrough
    Capability.familyChoiceProjection Capability.effectiveCapabilityWitness → ⊥
sameFamilyChoiceStillCannotDetermineCapability =
  Capability.familyChoiceCannotDetermineEffectiveCapability

record TakeupStratificationBoundary : Set where
  constructor takeupStratificationBoundary
  field
    equalAvailabilityMeansEqualUptake : Bool
    equalAvailabilityMeansEqualUptakeIsFalse :
      equalAvailabilityMeansEqualUptake ≡ false
    equalAvailabilityMeansEqualLabourEffect : Bool
    equalAvailabilityMeansEqualLabourEffectIsFalse :
      equalAvailabilityMeansEqualLabourEffect ≡ false
    stratifiedAuditRequired : Bool
    stratifiedAuditRequiredIsTrue : stratifiedAuditRequired ≡ true

canonicalTakeupStratificationBoundary : TakeupStratificationBoundary
canonicalTakeupStratificationBoundary =
  takeupStratificationBoundary false refl false refl true refl
