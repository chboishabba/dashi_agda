{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as H1

oneTheoremField :
  H1.canonicalH1HasOneTheoremBearingField ≡ true
oneTheoremField = refl

noPublishedWrapper :
  H1.publishedLocalizationWrapperMandatoryForCanonicalH1 ≡ false
noPublishedWrapper = refl

noMagnitudeApplicability :
  H1.sourceMagnitudeApplicabilityMandatoryForCanonicalH1 ≡ false
noMagnitudeApplicability = refl

noRootApplicability :
  H1.sourceRootApplicabilityMandatoryForCanonicalH1 ≡ false
noRootApplicability = refl

noDistanceApplicability :
  H1.sourceDistanceApplicabilityMandatoryForCanonicalH1 ≡ false
noDistanceApplicability = refl

noIndependentDirectShell :
  H1.independentDirectT5ShellMandatoryAfterH1 ≡ false
noIndependentDirectShell = refl

noFreshEstimate :
  H1.h1NewAnalyticEstimateIntroduced ≡ false
noFreshEstimate = refl

promotionFailClosed :
  H1.clayPromotion ≡ false
promotionFailClosed = refl
