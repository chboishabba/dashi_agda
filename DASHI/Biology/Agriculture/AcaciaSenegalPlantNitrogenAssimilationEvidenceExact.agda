module DASHI.Biology.Agriculture.AcaciaSenegalPlantNitrogenAssimilationEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESExact as Edaphic
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry
import DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact as Nodulation

------------------------------------------------------------------------
-- ACACIA-SPECIFIC PLANT NITROGEN ASSIMILATION EVIDENCE
--
-- This owner distinguishes a positive Acacia-specific evidence payment from the
-- generic BNF dependency ladder. Foliar natural-abundance 15N / N-derived-from-
-- atmosphere measurements are integrative plant-level evidence, but they are
-- not a direct molecular transfer-flux measurement, a seasonal whole-plant N
-- budget, an ecosystem soil-N balance or deployment authority.
------------------------------------------------------------------------

naturalPopulationDOI : String
naturalPopulationDOI = Edaphic.isaac2011DOI

phosphorusExperimentDOI : String
phosphorusExperimentDOI = Edaphic.isaacHarmandDrevon2011DOI

phosphorusExperimentPMID : String
phosphorusExperimentPMID = Edaphic.isaacHarmandDrevon2011PMID

naturalPopulationSource : Attribution.AttributedSource
naturalPopulationSource = Edaphic.isaacEtAl2011

phosphorusExperimentSource : Attribution.AttributedSource
phosphorusExperimentSource = Edaphic.isaacHarmandDrevon2011

data PlantNitrogenEvidenceRole : Set where
  foliarNaturalAbundance15N : PlantNitrogenEvidenceRole
  nitrogenDerivedFromAtmosphereEstimate : PlantNitrogenEvidenceRole
  plantNitrogenContent : PlantNitrogenEvidenceRole
  sourceInterpretation : PlantNitrogenEvidenceRole

record PlantFixedNEvidence : Set where
  constructor plant-fixed-n-evidence
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    observerRole : PlantNitrogenEvidenceRole
    plantCompartment : String
    methodReading : String
    contextReading : String
    supportsPlantLevelFixedNContribution : Bool
    isDirectMolecularTransferFlux : Bool
    isSeasonalWholePlantNBalance : Bool
    isEcosystemSoilNBalance : Bool
open PlantFixedNEvidence public

naturalPopulationFoliarEvidence : PlantFixedNEvidence
naturalPopulationFoliarEvidence = plant-fixed-n-evidence
  naturalPopulationSource
  naturalPopulationDOI
  nitrogenDerivedFromAtmosphereEstimate
  "foliar / plant tissue nitrogen observation"
  "foliar 15N natural-abundance based estimate of N2-fixation contribution"
  "natural Acacia senegal populations indexed by tree age and soil phosphorus in Baringo, Kenya"
  true false false false

phosphorusExperimentFoliarEvidence : PlantFixedNEvidence
phosphorusExperimentFoliarEvidence = plant-fixed-n-evidence
  phosphorusExperimentSource
  phosphorusExperimentDOI
  nitrogenDerivedFromAtmosphereEstimate
  "Acacia senegal seedling plant nitrogen observation"
  "15N natural-abundance estimate of nitrogen derived from atmosphere alongside plant N content"
  "controlled sand culture with low/mid/high phosphorus and uniform non-limiting nitrogen addition"
  true false false false

------------------------------------------------------------------------
-- Positive local evidence does not mutate the canonical global ladder.
------------------------------------------------------------------------

genericPlantAssimilationStillOpen :
  Chemistry.stageClosed Chemistry.plantAssimilation ≡ false
genericPlantAssimilationStillOpen = refl

noduleToDeliveryFirewallReused :
  Nodulation.activeNitrogenaseImpliesIntegratedFixedNDelivery
    Nodulation.canonicalNodulationBoundary ≡ false
noduleToDeliveryFirewallReused = refl

record PlantNitrogenAssimilationBoundary : Set where
  constructor plant-nitrogen-assimilation-boundary
  field
    acaciaSpecificPlantFixedNContributionEvidence : Bool
    foliarIsotopeEvidenceEqualsDirectTransferFlux : Bool
    genericPlantAssimilationStageClosed : Bool
    plantFixedNContributionCreatesSeasonalPlantNBalance : Bool
    plantFixedNContributionCreatesEcosystemSoilNBalance : Bool
    plantFixedNContributionCreatesFertilizerSubstitution : Bool
    plantFixedNContributionCreatesDeploymentAuthority : Bool
    sourceContextAndObserverMustRemainIndexed : Bool
    naturalPopulationAndSandCultureAreSameEmpiricalObject : Bool
open PlantNitrogenAssimilationBoundary public

canonicalPlantNBoundary : PlantNitrogenAssimilationBoundary
canonicalPlantNBoundary = plant-nitrogen-assimilation-boundary
  true false false false false false false true false

acaciaPlantLevelEvidencePaid :
  acaciaSpecificPlantFixedNContributionEvidence canonicalPlantNBoundary ≡ true
acaciaPlantLevelEvidencePaid = refl

genericAssimilationNotPromoted :
  genericPlantAssimilationStageClosed canonicalPlantNBoundary ≡ false
genericAssimilationNotPromoted = refl

attributionRule : String
attributionRule =
  "Isaac, Harmand, Lesueur & Lelon 2011 (DOI 10.1016/j.foreco.2010.11.011) owns its natural-population foliar-15N/fixation-context propositions. Isaac, Harmand & Drevon 2011 (DOI 10.1016/j.jplph.2010.10.011; PMID 21211863) owns its controlled phosphorus-gradient plant-N and N-derived-from-atmosphere propositions. DASHI owns only the evidence-role typing and promotion boundary. Plant-level isotope evidence is not relabelled as a direct nitrogenase-to-plant molecular transfer flux, seasonal N balance, soil-N balance, fertilizer substitution or intervention authority."
