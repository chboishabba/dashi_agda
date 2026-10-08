module DASHI.Governance.BoloBoloDerivedScaleEnvelopeRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloDerivedScaleEnvelopeExact as Scale

kanaBundleLowerPinned : Scale.kanaBundleLower Scale.canonicalDerivedScaleEnvelope ≡ 300
kanaBundleLowerPinned = refl

kanaBundleUpperPinned : Scale.kanaBundleUpper Scale.canonicalDerivedScaleEnvelope ≡ 600
kanaBundleUpperPinned = refl

tegaPopulationLowerPinned : Scale.tegaPopulationLower Scale.canonicalDerivedScaleEnvelope ≡ 5000
tegaPopulationLowerPinned = refl

tegaPopulationUpperPinned : Scale.tegaPopulationUpper Scale.canonicalDerivedScaleEnvelope ≡ 10000
tegaPopulationUpperPinned = refl

derivedNumbersNotSourceQuotes :
  Scale.derivedEnvelopeQuotedDirectlyFromSource Scale.canonicalDerivedScaleBoundary ≡ false
derivedNumbersNotSourceQuotes = refl

noOptimalityPromotion :
  Scale.derivedEnvelopeProvesOptimalScale Scale.canonicalDerivedScaleBoundary ≡ false
noOptimalityPromotion = refl
