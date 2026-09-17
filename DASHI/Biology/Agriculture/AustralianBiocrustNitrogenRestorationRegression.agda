module DASHI.Biology.Agriculture.AustralianBiocrustNitrogenRestorationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianBiocrustNitrogenRestorationExact as B

munozRojas2018DOIPinned :
  B.munozRojasEtAl2018DOI ≡ "10.1016/j.scitotenv.2018.04.265"
munozRojas2018DOIPinned = refl

munozRojas2018PMIDPinned :
  B.munozRojasEtAl2018PMID ≡ "29913577"
munozRojas2018PMIDPinned = refl

chua2020DOIPinned :
  B.chuaEtAl2020DOI ≡ "10.1111/rec.13040"
chua2020DOIPinned = refl

williams2022DOIPinned :
  B.williamsEtAl2022DOI ≡ "10.3390/agronomy12010062"
williams2022DOIPinned = refl

cofre2026DOIPinned :
  B.cofreEtAl2026DOI ≡ "10.1007/s00374-025-01963-9"
cofre2026DOIPinned = refl

nFixingRoleNotVascularOnly :
  B.nFixingPioneerRoleImpliesVascularPlant B.canonicalBiocrustBoundary ≡ false
nFixingRoleNotVascularOnly = refl

biocrustCoverNotFlux :
  B.biocrustCoverImpliesMeasuredNFixationFlux B.canonicalBiocrustBoundary ≡ false
biocrustCoverNotFlux = refl

genesNotFlux :
  B.nFixationGeneFrequencyImpliesMeasuredNFixationFlux B.canonicalBiocrustBoundary ≡ false
genesNotFlux = refl

soilCarbonNotPlantN :
  B.soilCarbonGainImpliesPlantAvailableNitrogen B.canonicalBiocrustBoundary ≡ false
soilCarbonNotPlantN = refl

seedlingResponseNotTrajectory :
  B.bioPrimingSeedlingResponseImpliesFieldTrajectoryRecovery B.canonicalBiocrustBoundary ≡ false
seedlingResponseNotTrajectory = refl

managementContextRetained :
  B.fireGrazingSeasonSoilMayBeDropped B.canonicalBiocrustBoundary ≡ false
managementContextRetained = refl

acaciaLadderStillOpen :
  B.biocrustEvidenceClosesAcaciaBacterialFixedNFlux B.canonicalBiocrustBoundary ≡ false
acaciaLadderStillOpen = refl
