module DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasExact as P

sourceCountRegression :
  Source.sourceCount (Source.sources P.canonicalEisensteinDivisorPowerAtlas) ≡ 4
sourceCountRegression = refl

atlasNonPromoting :
  Source.atlasCreatesAuthority P.canonicalEisensteinDivisorPowerAtlas ≡ false
atlasNonPromoting = refl

sigma3OEISIsParityOnly : P.sigma3OEISParityOnly ≡ true
sigma3OEISIsParityOnly = refl

sigma5OEISIsParityOnly : P.sigma5OEISParityOnly ≡ true
sigma5OEISIsParityOnly = refl

classicalCoefficientAuthoritySeparated :
  P.classicalCoefficientAuthoritySeparatedFromFiniteArithmetic ≡ true
classicalCoefficientAuthoritySeparated = refl
