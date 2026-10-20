module DASHI.Cognition.ClinicToStreetsImplementationSOTAValidation where

open import DASHI.Core.Prelude

import DASHI.Cognition.ClinicToStreetsImplementationSOTAExact as Impl

implementationSourceCountRegression : Impl.implementationSourceCount ≡ 4
implementationSourceCountRegression = refl

largeScaleUseNotOutcomeRegression :
  Impl.largeScaleCFIImplementationEstablishesOutcomeBenefit
    Impl.canonicalImplementationSOTABoundary ≡ false
largeScaleUseNotOutcomeRegression = refl

smallPilotNotEfficacyRegression :
  Impl.smallPilotUtilityEstablishesComparativeEfficacy
    Impl.canonicalImplementationSOTABoundary ≡ false
smallPilotNotEfficacyRegression = refl

mvpDesignNotEffectRegression :
  Impl.mvpDesignEstablishesClinicalOutcomeEffect
    Impl.canonicalImplementationSOTABoundary ≡ false
mvpDesignNotEffectRegression = refl
