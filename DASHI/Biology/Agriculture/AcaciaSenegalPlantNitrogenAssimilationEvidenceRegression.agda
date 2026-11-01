module DASHI.Biology.Agriculture.AcaciaSenegalPlantNitrogenAssimilationEvidenceRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalPlantNitrogenAssimilationEvidenceExact as PlantN

naturalPopulationDOIPinned :
  PlantN.naturalPopulationDOI ≡ "10.1016/j.foreco.2010.11.011"
naturalPopulationDOIPinned = refl

phosphorusExperimentDOIPinned :
  PlantN.phosphorusExperimentDOI ≡ "10.1016/j.jplph.2010.10.011"
phosphorusExperimentDOIPinned = refl

varietyStudyDOIPinned :
  PlantN.githae2013DOI ≡ "10.1080/15324982.2013.784377"
varietyStudyDOIPinned = refl

provenanceTemporalStudyDOIPinned :
  PlantN.raddad2005DOI ≡ "10.1007/s11104-005-2152-4"
provenanceTemporalStudyDOIPinned = refl

foliarNdfaIsPlantLevelEvidence :
  PlantN.acaciaSpecificPlantFixedNContributionEvidence PlantN.canonicalPlantNBoundary ≡ true
foliarNdfaIsPlantLevelEvidence = refl

foliarNdfaIsNotDirectMolecularTransferFlux :
  PlantN.foliarIsotopeEvidenceEqualsDirectTransferFlux PlantN.canonicalPlantNBoundary ≡ false
foliarNdfaIsNotDirectMolecularTransferFlux = refl

varietyIdentityAloneNotAdequate :
  PlantN.speciesIdentityAloneAdequateForFixedNContribution PlantN.canonicalPlantNBoundary ≡ false
varietyIdentityAloneNotAdequate = refl

provenanceAloneNotAdequateWithoutAge :
  PlantN.provenanceIdentityAloneAdequateWithoutAge PlantN.canonicalPlantNBoundary ≡ false
provenanceAloneNotAdequateWithoutAge = refl

fixedNContributionRemainsTimeIndexed :
  PlantN.fixedNContributionMustRemainTimeIndexed PlantN.canonicalPlantNBoundary ≡ true
fixedNContributionRemainsTimeIndexed = refl

noduleAssessmentNotSameMeasurement :
  PlantN.noduleAssessmentEqualsFoliarFixationEstimate PlantN.canonicalPlantNBoundary ≡ false
noduleAssessmentNotSameMeasurement = refl

genericPlantAssimilationRemainsOpen :
  PlantN.genericPlantAssimilationStageClosed PlantN.canonicalPlantNBoundary ≡ false
genericPlantAssimilationRemainsOpen = refl

plantContributionDoesNotCreateSeasonalBalance :
  PlantN.plantFixedNContributionCreatesSeasonalPlantNBalance PlantN.canonicalPlantNBoundary ≡ false
plantContributionDoesNotCreateSeasonalBalance = refl
