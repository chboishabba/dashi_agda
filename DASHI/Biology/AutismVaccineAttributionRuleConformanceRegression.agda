module DASHI.Biology.AutismVaccineAttributionRuleConformanceRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.AutismVaccineAttributionRuleConformanceExact as C

citationAndSourceIdentityDoNotCreateAuthorityRegression :
  C.citationCreatesProof C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.citationCreatesAuthority C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
citationAndSourceIdentityDoNotCreateAuthorityRegression = refl , refl

supportPriorityCorrectnessRemainSeparateRegression :
  C.scientificSupportProvesPriority C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.priorityProvesCorrectness C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
supportPriorityCorrectnessRemainSeparateRegression = refl , refl

contactExposureDoesNotBecomeDerivationRegression :
  C.contactOrExposureProvesDerivation C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.contactOrExposureProvesPlagiarism C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
contactExposureDoesNotBecomeDerivationRegression = refl , refl

unknownAndUnpaidDoNotBecomeZeroRegression :
  C.unknownCoordinateEqualsZero C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.unpaidCoordinateEqualsZero C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
unknownAndUnpaidDoNotBecomeZeroRegression = refl , refl

sourceAndDASHISynthesisRemainSeparateRegression :
  C.externalSourceOwnsDASHISynthesis C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
sourceAndDASHISynthesisRemainSeparateRegression = refl
