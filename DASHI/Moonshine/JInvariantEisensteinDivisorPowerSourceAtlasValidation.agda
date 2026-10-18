module DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasExact as P

sourceCountRegression :
  Source.sourceCount (Source.sources P.canonicalEisensteinDivisorPowerAtlas) ≡ 6
sourceCountRegression = refl

atlasNonPromoting :
  Source.atlasCreatesAuthority P.canonicalEisensteinDivisorPowerAtlas ≡ false
atlasNonPromoting = refl

sigma3OEISIsParityOnly : P.sigma3OEISParityOnly ≡ true
sigma3OEISIsParityOnly = refl

sigma5OEISIsParityOnly : P.sigma5OEISParityOnly ≡ true
sigma5OEISIsParityOnly = refl

e4OEISIsParityOnly : P.e4OEISParityOnly ≡ true
e4OEISIsParityOnly = refl

e6OEISIsParityOnly : P.e6OEISParityOnly ≡ true
e6OEISIsParityOnly = refl

classicalCoefficientAuthoritySeparated :
  P.classicalCoefficientAuthoritySeparatedFromFiniteArithmetic ≡ true
classicalCoefficientAuthoritySeparated = refl
