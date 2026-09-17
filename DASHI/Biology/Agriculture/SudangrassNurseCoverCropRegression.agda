module DASHI.Biology.Agriculture.SudangrassNurseCoverCropRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.SudangrassNurseCoverCropExact as S

kaneko2023Pinned : S.kaneko2023DOI ≡ "10.1111/grs.12391"
kaneko2023Pinned = refl

guretzky2021Pinned : S.guretzky2021DOI ≡ "10.3390/agronomy11122449"
guretzky2021Pinned = refl

burt2025Pinned : S.burt2025DOI ≡ "10.1002/cft2.70055"
burt2025Pinned = refl

paudel2021Pinned : S.paudelEtAl2021DOI ≡ "10.3390/microorganisms9091831"
paudel2021Pinned = refl

temporaryCoverNotPerennialRecovery : S.temporaryCoverImpliesPerennialRecovery S.canonicalSudangrassBoundary ≡ false
temporaryCoverNotPerennialRecovery = refl

biomassNotBiodiversity : S.biomassIncreaseImpliesBiodiversityRecovery S.canonicalSudangrassBoundary ≡ false
biomassNotBiodiversity = refl

weedSuppressionNotRestoration : S.weedSuppressionImpliesNativeRestoration S.canonicalSudangrassBoundary ≡ false
weedSuppressionNotRestoration = refl

soilHealthNotCashCropYield : S.soilHealthImprovementImpliesCashCropYieldGain S.canonicalSudangrassBoundary ≡ false
soilHealthNotCashCropYield = refl

microbialBiomassNotPathogenPopulationSuppression :
  S.microbialProfileImprovementImpliesTargetPathogenPopulationSuppression S.canonicalSudangrassBoundary ≡ false
microbialBiomassNotPathogenPopulationSuppression = refl

varietyAgeTerminationRetained :
  S.varietyAgeAndTerminationMethodMustRemainIndexed S.canonicalSudangrassBoundary ≡ true
varietyAgeTerminationRetained = refl

reversibilityRetained : S.terminationAndReversibilityMustRemainIndexed S.canonicalSudangrassBoundary ≡ true
reversibilityRetained = refl
