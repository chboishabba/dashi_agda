module DASHI.Biology.Agriculture.AustralianAcaciaGrassSoilNitrogenLegacyRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianAcaciaGrassSoilNitrogenLegacyExact as N

allen2016DOIPinned : N.allenEtAl2016DOI ≡ "10.1071/RJ16009"
allen2016DOIPinned = refl

pringle2016DOIPinned : N.pringleEtAl2016DOI ≡ "10.1071/RJ16010"
pringle2016DOIPinned = refl

thornton2021DOIPinned : N.thorntonShrestha2021DOI ≡ "10.1071/SR20088"
thornton2021DOIPinned = refl

kirschbaum2008DOIPinned :
  N.kirschbaumEtAl2008DOI ≡ "10.1016/j.soilbio.2007.09.003"
kirschbaum2008DOIPinned = refl

fertilityPulseNotPersistence :
  N.initialPostClearingFertilityPulseImpliesSustainedFertility N.canonicalAcaciaGrassSoilBoundary ≡ false
fertilityPulseNotPersistence = refl

vegetationNotSoilRecovery :
  N.regrowthVegetationSignalImpliesRecoveredSoilCarbonNitrogen N.canonicalAcaciaGrassSoilBoundary ≡ false
vegetationNotSoilRecovery = refl

isotopeNotPool :
  N.recoveredDelta13CImpliesRecoveredTotalOrganicCarbon N.canonicalAcaciaGrassSoilBoundary ≡ false
isotopeNotPool = refl

landCoverNotBNFFlux :
  N.acaciaLandCoverImpliesMeasuredBiologicalNitrogenFixationFlux N.canonicalAcaciaGrassSoilBoundary ≡ false
landCoverNotBNFFlux = refl

historyRetained :
  N.clearingFireCroppingGrazingHistoryMayBeDropped N.canonicalAcaciaGrassSoilBoundary ≡ false
historyRetained = refl

modelNotMeasurement :
  N.modelReproductionCreatesDirectFluxMeasurement N.canonicalAcaciaGrassSoilBoundary ≡ false
modelNotMeasurement = refl
