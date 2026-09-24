module DASHI.Biology.Agriculture.AustralianRestorationSoilFunctionObserverRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianRestorationSoilFunctionObserverExact as O

dagui2022Pinned : O.daguiEtAl2022DOI ≡ "10.1111/rec.13738"
dagui2022Pinned = refl

microbialCompositionNotFunction :
  O.microbialCompositionAloneDeterminesSoilFunctionality O.canonicalSoilFunctionObserverBoundary ≡ false
microbialCompositionNotFunction = refl

respirationNotPlantFunction :
  O.respirationAloneDeterminesPlantGrowthFunctionality O.canonicalSoilFunctionObserverBoundary ≡ false
respirationNotPlantFunction = refl

singleMetricNotUniversal :
  O.anySingleBioticMetricDeterminesSoilFunctionality O.canonicalSoilFunctionObserverBoundary ≡ false
singleMetricNotUniversal = refl

siteBiomeRetained :
  O.siteBiomeStockpileAgeAndOriginMustRemainIndexed O.canonicalSoilFunctionObserverBoundary ≡ true
siteBiomeRetained = refl

observerMethodRetained :
  O.observerMethodMustRemainIndexed O.canonicalSoilFunctionObserverBoundary ≡ true
observerMethodRetained = refl

crossMineNotUniversal :
  O.oneMineResponseCreatesUniversalTopsoilResponse O.canonicalSoilFunctionObserverBoundary ≡ false
crossMineNotUniversal = refl
