module DASHI.Analysis.RiemannUniversalEvenConeFinalTaperLocalizationValidationExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannUniversalEvenConeFinalTaperLocalizationExact as P

localizationRegression :
  P.UniversalEvenConeFinalTaperLocalizationBoundary.onlyNewTaperWeldIsSourceToOff
    P.canonicalUniversalEvenConeFinalTaperLocalizationBoundary
  ≡ true
  × P.UniversalEvenConeFinalTaperLocalizationBoundary.offToGammaReuseAlreadyOwned
    P.canonicalUniversalEvenConeFinalTaperLocalizationBoundary
  ≡ true
  × P.UniversalEvenConeFinalTaperLocalizationBoundary.offToClusterReuseAlreadyOwned
    P.canonicalUniversalEvenConeFinalTaperLocalizationBoundary
  ≡ true
localizationRegression = refl , refl , refl

nonPromotionRegression :
  P.UniversalEvenConeFinalTaperLocalizationBoundary.sourceToOffSameObjectWeldPaid
    P.canonicalUniversalEvenConeFinalTaperLocalizationBoundary
  ≡ false
  × P.UniversalEvenConeFinalTaperLocalizationBoundary.leanSourceExistenceCreatesWeld
    P.canonicalUniversalEvenConeFinalTaperLocalizationBoundary
  ≡ false
  × P.UniversalEvenConeFinalTaperLocalizationBoundary.oeisCreatesWeld
    P.canonicalUniversalEvenConeFinalTaperLocalizationBoundary
  ≡ false
nonPromotionRegression = refl , refl , refl
