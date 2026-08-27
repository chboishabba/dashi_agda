module DASHI.Governance.Fanning2022SocialIndicatorRevisionExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustIndicatorSystemExact as ONeill
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- FANNING ET AL. 2022: SOCIAL INDICATOR REVISION BOUNDARY
--
-- The longitudinal study retains an eleven-coordinate social vocabulary but
-- does not preserve every 2018 indicator definition unchanged.
--
-- Two source-visible revisions matter especially:
--
-- 1. longevity:
--    O'Neill 2018 uses healthy life expectancy with threshold 65 years.
--    Fanning 2022 uses overall life expectancy because a suitable historical
--    healthy-life-expectancy series is unavailable.  The threshold is 74 years,
--    calibrated from the roughly nine-year average gap between life expectancy
--    and healthy life expectancy.
--
-- 2. income poverty:
--    the longitudinal study uses the share of people below the World Bank
--    $5.50/day line in 2011 PPP rather than the earlier $1.90/day extreme-
--    poverty line.  The source itself cautions that monetary poverty thresholds
--    interact with context-specific costs and provisioning arrangements.
--
-- Hence "same eleven social slots" does not imply "same measurement semantics".
------------------------------------------------------------------------

data LongevityMeasure : Set where
  healthyLifeExpectancy overallLifeExpectancy : LongevityMeasure

data PovertyLineRole : Set where
  extremePoverty190 broaderPoverty550 : PovertyLineRole

record LongevityRevision : Set where
  constructor longevityRevision
  field
    earlierMeasure : LongevityMeasure
    longitudinalMeasure : LongevityMeasure
    earlierThresholdYears : Nat
    longitudinalThresholdYears : Nat

canonicalLongevityRevision : LongevityRevision
canonicalLongevityRevision =
  longevityRevision healthyLifeExpectancy overallLifeExpectancy 65 74

earlierAndLongitudinalLongevityMeasuresDiffer :
  healthyLifeExpectancy ≡ overallLifeExpectancy → ⊥
earlierAndLongitudinalLongevityMeasuresDiffer ()

record PovertyRevision : Set where
  constructor povertyRevision
  field
    earlierLine : PovertyLineRole
    longitudinalLine : PovertyLineRole
    earlierCentsPerDay2011PPP : Nat
    longitudinalCentsPerDay2011PPP : Nat

canonicalPovertyRevision : PovertyRevision
canonicalPovertyRevision = povertyRevision extremePoverty190 broaderPoverty550 190 550

earlierAndLongitudinalPovertyLinesDiffer :
  extremePoverty190 ≡ broaderPoverty550 → ⊥
earlierAndLongitudinalPovertyLinesDiffer ()

-- The 2018 social vocabulary still provides the genealogical slot identity.
longevitySlot : ONeill.SocialIndicator
longevitySlot = ONeill.healthyLifeExpectancy

incomeSlot : ONeill.SocialIndicator
incomeSlot = ONeill.income

source : Sources.SourceReference
source = Sources.fanning2022

record FanningSocialIndicatorRevisionBoundary : Set where
  constructor fanningSocialIndicatorRevisionBoundary
  field
    socialVocabularyStillHasElevenSlots : Bool
    socialVocabularyStillHasElevenSlotsIsTrue :
      socialVocabularyStillHasElevenSlots ≡ true
    allElevenMeasurementDefinitionsAreUnchangedFrom2018 : Bool
    allElevenMeasurementDefinitionsAreUnchangedFrom2018IsFalse :
      allElevenMeasurementDefinitionsAreUnchangedFrom2018 ≡ false
    longitudinalLongevityUsesOverallLifeExpectancy : Bool
    longitudinalLongevityUsesOverallLifeExpectancyIsTrue :
      longitudinalLongevityUsesOverallLifeExpectancy ≡ true
    overallLifeExpectancyIsDefinitionallyHealthyLifeExpectancy : Bool
    overallLifeExpectancyIsDefinitionallyHealthyLifeExpectancyIsFalse :
      overallLifeExpectancyIsDefinitionallyHealthyLifeExpectancy ≡ false
    longitudinalPovertyLineIsEarlierExtremePovertyLine : Bool
    longitudinalPovertyLineIsEarlierExtremePovertyLineIsFalse :
      longitudinalPovertyLineIsEarlierExtremePovertyLine ≡ false
    monetaryPovertyThresholdAloneDeterminesNeedSatisfaction : Bool
    monetaryPovertyThresholdAloneDeterminesNeedSatisfactionIsFalse :
      monetaryPovertyThresholdAloneDeterminesNeedSatisfaction ≡ false

canonicalFanningSocialIndicatorRevisionBoundary :
  FanningSocialIndicatorRevisionBoundary
canonicalFanningSocialIndicatorRevisionBoundary =
  fanningSocialIndicatorRevisionBoundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
