module DASHI.Biology.Agriculture.AustralianGrasslandFireCompetitionHerbivoryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianGrasslandFireCompetitionHerbivoryExact as F

butlerFairfax2003DOIPinned :
  F.butlerFairfax2003DOI ≡ "10.1046/j.1442-8903.2003.00146.x"
butlerFairfax2003DOIPinned = refl

bellEtAl2022DOIPinned :
  F.bellEtAl2022DOI ≡ "10.1111/1365-2664.14192"
bellEtAl2022DOIPinned = refl

frenchEtAl2024DOIPinned :
  F.frenchEtAl2024DOI ≡ "10.1002/2688-8319.12355"
frenchEtAl2024DOIPinned = refl

rigbyEtAl2026DOIPinned :
  F.rigbyEtAl2026DOI ≡ "10.1111/aec.70211"
rigbyEtAl2026DOIPinned = refl

fireIsNotUniformlyRestorative :
  F.fireTreatmentAloneDeterminesNativeRecovery F.canonicalDisturbanceBoundary ≡ false
fireIsNotUniformlyRestorative = refl

soilContextCannotBeDropped :
  F.soilTypeAndNutrientContextMustRemainIndexed F.canonicalDisturbanceBoundary ≡ true
soilContextCannotBeDropped = refl

exoticFuelFeedbackCannotBeDropped :
  F.exoticGrassFuelFeedbackMayBeDropped F.canonicalDisturbanceBoundary ≡ false
exoticFuelFeedbackCannotBeDropped = refl

fireDoesNotReplaceRecruitmentContext :
  F.fireAloneOvercomesSeedBankAndRecruitmentLimitation F.canonicalDisturbanceBoundary ≡ false
fireDoesNotReplaceRecruitmentContext = refl

grazingIsNotUniformlyDegrading :
  F.herbivoryAlwaysReducesConservationOutcome F.canonicalDisturbanceBoundary ≡ false
grazingIsNotUniformlyDegrading = refl

sameFireDoesNotImplySameOutcome :
  F.sameFireTreatmentAcrossSoilsImpliesSameNativeResponse F.canonicalDisturbanceBoundary ≡ false
sameFireDoesNotImplySameOutcome = refl
