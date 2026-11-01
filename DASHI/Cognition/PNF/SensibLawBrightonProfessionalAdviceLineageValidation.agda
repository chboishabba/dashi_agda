module DASHI.Cognition.PNF.SensibLawBrightonProfessionalAdviceLineageValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawBrightonProfessionalAdviceLineageExact as Advice

matterAssertionsRemainAssertionsExact :
  Advice.BrightonProfessionalAdviceBoundary.matterAssertionsRemainAssertions
    Advice.canonicalBrightonProfessionalAdviceBoundary
  ≡ true
matterAssertionsRemainAssertionsExact = refl

professionalAdviceSeparateFromMatterFactsExact :
  Advice.BrightonProfessionalAdviceBoundary.professionalAdviceSeparateFromMatterFacts
    Advice.canonicalBrightonProfessionalAdviceBoundary
  ≡ true
professionalAdviceSeparateFromMatterFactsExact = refl

professionalAdviceSeparateFromTribunalFindingExact :
  Advice.BrightonProfessionalAdviceBoundary.professionalAdviceSeparateFromTribunalFinding
    Advice.canonicalBrightonProfessionalAdviceBoundary
  ≡ true
professionalAdviceSeparateFromTribunalFindingExact = refl

professionalAdviceSeparateFromStatutoryBreachExact :
  Advice.BrightonProfessionalAdviceBoundary.professionalAdviceSeparateFromStatutoryBreach
    Advice.canonicalBrightonProfessionalAdviceBoundary
  ≡ true
professionalAdviceSeparateFromStatutoryBreachExact = refl

proceduralAdviceSeparateFromCausationExact :
  Advice.BrightonProfessionalAdviceBoundary.proceduralAdviceSeparateFromCausation
    Advice.canonicalBrightonProfessionalAdviceBoundary
  ≡ true
proceduralAdviceSeparateFromCausationExact = refl

noticeTimingSeparateFromMotiveExact :
  Advice.BrightonProfessionalAdviceBoundary.noticeTimingSeparateFromMotive
    Advice.canonicalBrightonProfessionalAdviceBoundary
  ≡ true
noticeTimingSeparateFromMotiveExact = refl
