module DASHI.Chemistry.Spectroscopy.CryogenicTagPerturbationAndAssignmentDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Generic messenger-tag perturbation and assignment-depth owner.
-- Sources:
-- Christopher J. Johnson et al., "Communication: He-tagged vibrational spectra ... quantifying tag effects in cryogenic ion vibrational predissociation spectroscopy",
-- J. Chem. Phys. 140, 221101 (2014), DOI 10.1063/1.4880475.
-- J. Phys. Chem. A 122 (2018) 8037-8046, "Vibrational Predissociation Spectroscopy of Cold Protonated Tryptophan with Different Messenger Tags",
-- DOI 10.1021/acs.jpca.8b07532.
-- J. Phys. Chem. A 128 (2024) 7137-7144, "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects",
-- DOI 10.1021/acs.jpca.4c03552.

data TagCoordinate : Set where
  tagSpecies
  tagBindingEnergy
  tagNumber
  tagSite
  trappingTemperature
  dissociationThreshold
  photonEnergy
  actionYield
  : TagCoordinate

data AssignmentCoordinate : Set where
  conformerPopulation
  candidateGeometry
  harmonicFrequencyModel
  anharmonicCorrection
  intensityModel
  tagPerturbationModel
  holeBurningSeparation
  : AssignmentCoordinate

record TagPerturbationProfile : Set where
  constructor tag-perturbation-profile
  field
    tagCoordinates : List TagCoordinate
    assignmentCoordinates : List AssignmentCoordinate
    sourceReference : String
    boundedReading : String

open TagPerturbationProfile public

canonicalTagPerturbationProfile : TagPerturbationProfile
canonicalTagPerturbationProfile = tag-perturbation-profile
  (tagSpecies ∷ tagBindingEnergy ∷ tagNumber ∷ tagSite ∷ trappingTemperature ∷ dissociationThreshold ∷ photonEnergy ∷ actionYield ∷ [])
  (conformerPopulation ∷ candidateGeometry ∷ harmonicFrequencyModel ∷ anharmonicCorrection ∷ intensityModel ∷ tagPerturbationModel ∷ holeBurningSeparation ∷ [])
  "Johnson et al. JCP 2014 DOI 10.1063/1.4880475; JPCA 2018 DOI 10.1021/acs.jpca.8b07532; JPCA 2024 DOI 10.1021/acs.jpca.4c03552"
  "Messenger tags can shift frequencies, alter intensities and select binding sites/conformers; tag identity, number and binding energy are part of the measurement model rather than invisible spectators."

record ActionResponseBoundary : Set where
  constructor action-response-boundary
  field
    actionIntensityEqualsLinearAbsorptionIntensity : Bool
    actionIntensityEqualsLinearAbsorptionIntensityIsFalse : actionIntensityEqualsLinearAbsorptionIntensity ≡ false
    differentTagsAlwaysGiveIdenticalSpectrum : Bool
    differentTagsAlwaysGiveIdenticalSpectrumIsFalse : differentTagsAlwaysGiveIdenticalSpectrum ≡ false
    oneDFTMatchImpliesUniqueConformerAssignment : Bool
    oneDFTMatchImpliesUniqueConformerAssignmentIsFalse : oneDFTMatchImpliesUniqueConformerAssignment ≡ false
    weakTagCanStillPerturbMeasuredResponse : Bool
    weakTagCanStillPerturbMeasuredResponseIsTrue : weakTagCanStillPerturbMeasuredResponse ≡ true

canonicalActionResponseBoundary : ActionResponseBoundary
canonicalActionResponseBoundary = action-response-boundary false refl false refl false refl true refl

data TagAssignmentReverseTarget : Set where
  acquireTagBindingEnergy
  acquireTagSiteDistribution
  acquireTagNumberDependence
  acquireTemperatureDependence
  acquireIntensityResponseModel
  acquireConformerSelectiveSpectrum
  acquireAnharmonicCalculation
  acquireCrossTagReplication
  : TagAssignmentReverseTarget
