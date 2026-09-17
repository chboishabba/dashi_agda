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
-- Positive Acacia plant-level isotope evidence remains distinct from a direct
-- molecular transfer flux, whole-season N budget, ecosystem balance or generic
-- BNF-ladder closure.
------------------------------------------------------------------------

naturalPopulationDOI : String
naturalPopulationDOI = Edaphic.isaac2011DOI

phosphorusExperimentDOI : String
phosphorusExperimentDOI = Edaphic.isaacHarmandDrevon2011DOI

phosphorusExperimentPMID : String
phosphorusExperimentPMID = Edaphic.isaacHarmandDrevon2011PMID

githae2013DOI : String
githae2013DOI = "10.1080/15324982.2013.784377"

raddad2005DOI : String
raddad2005DOI = "10.1007/s11104-005-2152-4"

naturalPopulationSource : Attribution.AttributedSource
naturalPopulationSource = Edaphic.isaacEtAl2011

phosphorusExperimentSource : Attribution.AttributedSource
phosphorusExperimentSource = Edaphic.isaacHarmandDrevon2011

githaeEtAl2013 : Attribution.AttributedSource
githaeEtAl2013 = Attribution.mkDOISource
  "Eunice W. Githae; Charles K. K. Gachene; Jesse T. Njoka; Stephen F. Omondi"
  "Nitrogen Fixation by Natural Populations of Acacia Senegal in the Drylands of Kenya Using 15N Natural Abundance"
  "Arid Land Research and Management 27(4):327-336"
  "2013"
  githae2013DOI
  "https://doi.org/10.1080/15324982.2013.784377"
  Attribution.academicArticleSource
  "Primary dryland Kenya source estimating N2 fixation for three Acacia senegal varieties using leaf 15N natural abundance while separately collecting soil/nodule observations. The source reports significant variation in amount of N2 fixed among varieties."
  Attribution.publicAttribution

raddadEtAl2005 : Attribution.AttributedSource
raddadEtAl2005 = Attribution.mkDOISource
  "El Amin Yousif Raddad; Ahmed Ali Salih; Mohamed Ahmed El Fadl; Vesa Kaarakka; Olavi Luukkanen"
  "Symbiotic nitrogen fixation in eight Acacia senegal provenances in dryland clays of the Blue Nile Sudan estimated by the 15N natural abundance method"
  "Plant and Soil 275(1-2):261-269"
  "2005"
  raddad2005DOI
  "https://doi.org/10.1007/s11104-005-2152-4"
  Attribution.academicArticleSource
  "Primary Sudan source estimating Acacia senegal N derived from atmosphere by 15N natural abundance across eight provenances and multiple tree ages. It reports provenance- and age-indexed variation, including increased Ndfa with age and provenance-specific above-ground fixed-N contribution to foliage."
  Attribution.publicAttribution

data PlantNitrogenEvidenceRole : Set where
  foliarNaturalAbundance15N : PlantNitrogenEvidenceRole
  nitrogenDerivedFromAtmosphereEstimate : PlantNitrogenEvidenceRole
  plantNitrogenContent : PlantNitrogenEvidenceRole
  noduleAssessment : PlantNitrogenEvidenceRole
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

githaeVarietyFoliarEvidence : PlantFixedNEvidence
githaeVarietyFoliarEvidence = plant-fixed-n-evidence
  githaeEtAl2013
  githae2013DOI
  nitrogenDerivedFromAtmosphereEstimate
  "leaves from naturally occurring Acacia senegal varieties"
  "leaf 15N natural-abundance estimate with a neighboring non-legume reference; nodule assessment retained as a separate observation"
  "three Acacia senegal varieties across Kenyan dryland sites"
  true false false false

raddadProvenanceTemporalFoliarEvidence : PlantFixedNEvidence
raddadProvenanceTemporalFoliarEvidence = plant-fixed-n-evidence
  raddadEtAl2005
  raddad2005DOI
  nitrogenDerivedFromAtmosphereEstimate
  "foliage from Acacia senegal provenances in Blue Nile dryland clay"
  "15N natural-abundance Ndfa estimate with a non-N2-fixing reference; above-ground fixed-N contribution to foliage retained as a plant-level derived quantity"
  "eight provenances measured across tree age; age and provenance remain explicit coordinates rather than being collapsed into species identity"
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
    speciesIdentityAloneAdequateForFixedNContribution : Bool
    provenanceIdentityAloneAdequateWithoutAge : Bool
    fixedNContributionMustRemainTimeIndexed : Bool
    noduleAssessmentEqualsFoliarFixationEstimate : Bool
    varietySiteAndObserverRemainIndexed : Bool
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
  true false false false true false true false false false false false true false

acaciaPlantLevelEvidencePaid :
  acaciaSpecificPlantFixedNContributionEvidence canonicalPlantNBoundary ≡ true
acaciaPlantLevelEvidencePaid = refl

genericAssimilationNotPromoted :
  genericPlantAssimilationStageClosed canonicalPlantNBoundary ≡ false
genericAssimilationNotPromoted = refl

attributionRule : String
attributionRule =
  "Isaac, Harmand, Lesueur & Lelon 2011 (DOI 10.1016/j.foreco.2010.11.011) owns its natural-population foliar-15N/fixation-context propositions. Isaac, Harmand & Drevon 2011 (DOI 10.1016/j.jplph.2010.10.011; PMID 21211863) owns its controlled phosphorus-gradient plant-N and N-derived-from-atmosphere propositions. Githae, Gachene, Njoka & Omondi 2013 (DOI 10.1080/15324982.2013.784377) owns its variety/site-indexed leaf-15N fixation estimates and separate nodule observations. Raddad, Salih, El Fadl, Kaarakka & Luukkanen 2005 (DOI 10.1007/s11104-005-2152-4) owns its eight-provenance, age-indexed 15N/Ndfa and above-ground foliage fixed-N contribution propositions in Blue Nile Sudan. DASHI owns only the evidence-role typing and promotion boundary. Plant-level isotope evidence is not relabelled as a direct molecular transfer flux, whole-season N balance, soil-N balance, fertilizer substitution or intervention authority."
