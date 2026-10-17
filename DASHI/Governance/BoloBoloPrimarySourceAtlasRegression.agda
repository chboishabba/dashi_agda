module DASHI.Governance.BoloBoloPrimarySourceAtlasRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Source

boloApproximateScaleIsSourceAttributed :
  Source.boloApproximatePopulation Source.canonicalBoloBoloPrimarySourceAtlas ≡ 500
boloApproximateScaleIsSourceAttributed = refl

kanaLowerBoundPinned :
  Source.kanaLowerPopulation Source.canonicalBoloBoloPrimarySourceAtlas ≡ 15
kanaLowerBoundPinned = refl

kanaUpperBoundPinned :
  Source.kanaUpperPopulation Source.canonicalBoloBoloPrimarySourceAtlas ≡ 30
kanaUpperBoundPinned = refl

boloContainsAboutTwentyKana :
  Source.boloApproximateKanaCount Source.canonicalBoloBoloPrimarySourceAtlas ≡ 20
boloContainsAboutTwentyKana = refl

tegaLowerBoloCountPinned :
  Source.tegaLowerBoloCount Source.canonicalBoloBoloPrimarySourceAtlas ≡ 10
tegaLowerBoloCountPinned = refl

tegaUpperBoloCountPinned :
  Source.tegaUpperBoloCount Source.canonicalBoloBoloPrimarySourceAtlas ≡ 20
tegaUpperBoloCountPinned = refl

sizesAreNotEmpiricalOptima :
  Source.sourceNumbersProveEmpiricalOptimality Source.canonicalBoloBoloPrimarySourceBoundary ≡ false
sizesAreNotEmpiricalOptima = refl
