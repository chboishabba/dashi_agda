module DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Dryland
import DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationExact as BNFLES

------------------------------------------------------------------------
-- ACACIA SENEGAL BNF EDAPHIC / LES CONTEXT
--
-- External source propositions remain source-owned. DASHI owns only the typed
-- crosswalk, finite information-loss witnesses and no-promotion boundaries.
--
-- Source A:
-- Abaker et al. (2018), PeerJ 6:e5232.
-- DOI 10.7717/peerj.5232; PMID 30018862; PMCID PMC6044267.
-- Same broad Sudan plantation programme as the dryland hydrology work, but a
-- distinct publication/measurement object.
--
-- Source B:
-- Isaac, Harmand, Lesueur & Lelon (2011), Forest Ecology and Management
-- 261(3):582-588. DOI 10.1016/j.foreco.2010.11.011.
--
-- Source C:
-- Isaac, Harmand & Drevon (2011), Journal of Plant Physiology 168(8):776-781.
-- DOI 10.1016/j.jplph.2010.10.011; PMID 21211863.
------------------------------------------------------------------------

peerJ2018DOI : String
peerJ2018DOI = "10.7717/peerj.5232"

peerJ2018PMID : String
peerJ2018PMID = "30018862"

peerJ2018PMCID : String
peerJ2018PMCID = "PMC6044267"

isaac2011DOI : String
isaac2011DOI = "10.1016/j.foreco.2010.11.011"

isaacHarmandDrevon2011DOI : String
isaacHarmandDrevon2011DOI = "10.1016/j.jplph.2010.10.011"

isaacHarmandDrevon2011PMID : String
isaacHarmandDrevon2011PMID = "21211863"

abakerEtAlPeerJ2018 : Attribution.AttributedSource
abakerEtAlPeerJ2018 = Attribution.mkDOISource
  "Wafa E. Abaker; Frank Berninger; Gustavo Saiz; Jukka Pumpanen; Mike Starr"
  "Linkages between soil carbon, soil fertility and nitrogen fixation in Acacia senegal plantations of varying age in Sudan"
  "PeerJ 6:e5232"
  "2018"
  peerJ2018DOI
  "https://pubmed.ncbi.nlm.nih.gov/30018862/"
  Attribution.academicArticleSource
  "Primary source for soil N/P/K, SOC and foliar delta-15N observations in Acacia/Senegalia senegal plantations and adjacent grasslands at two semi-arid Sudan sites. The source reports high foliar delta-15N and concludes N2 fixation was not an important contributor to plantation soil N in the studied system."
  Attribution.publicAttribution

isaacEtAl2011 : Attribution.AttributedSource
isaacEtAl2011 = Attribution.mkDOISource
  "Marney E. Isaac; Jean-Michel Harmand; Didier Lesueur; Joseph K. Lelon"
  "Tree age and soil phosphorus conditions influence N2-fixation rates and soil N dynamics in natural populations of Acacia senegal"
  "Forest Ecology and Management 261(3):582-588"
  "2011"
  isaac2011DOI
  "https://doi.org/10.1016/j.foreco.2010.11.011"
  Attribution.academicArticleSource
  "Primary source for age- and soil-phosphorus-indexed Acacia senegal N2-fixation estimates using foliar 15N natural abundance and associated soil N/C observations in natural populations in Baringo, Kenya."
  Attribution.publicAttribution

isaacHarmandDrevon2011 : Attribution.AttributedSource
isaacHarmandDrevon2011 = Attribution.mkDOISource
  "Marney E. Isaac; Jean-Michel Harmand; Jean-Jacques Drevon"
  "Growth and nitrogen acquisition strategies of Acacia senegal seedlings under exponential phosphorus additions"
  "Journal of Plant Physiology 168(8):776-781"
  "2011"
  isaacHarmandDrevon2011DOI
  "https://pubmed.ncbi.nlm.nih.gov/21211863/"
  Attribution.academicArticleSource
  "Primary sand-culture source for Acacia senegal phosphorus-response and nitrogen-acquisition strategy under uniform non-limiting nitrogen addition. Higher phosphorus increased biomass and mineral-N acquisition but did not increase nodule number or N derived from atmosphere along the P gradient."
  Attribution.publicAttribution

record AcaciaEdaphicSourceIdentifiers : Set where
  constructor acacia-edaphic-source-identifiers
  field
    peerJPMID : String
    peerJPMCID : String
    isaacNaturalPopulationPMID : String
    isaacNaturalPopulationPMCID : String
    isaacPhosphorusExperimentPMID : String
    isaacPhosphorusExperimentPMCID : String
open AcaciaEdaphicSourceIdentifiers public

verifiedIdentifiers : AcaciaEdaphicSourceIdentifiers
verifiedIdentifiers = acacia-edaphic-source-identifiers
  peerJ2018PMID peerJ2018PMCID
  "not recorded by this atlas" "not recorded by this atlas"
  isaacHarmandDrevon2011PMID "not recorded by this atlas"

------------------------------------------------------------------------
-- Source-bounded qualitative readings.
------------------------------------------------------------------------

record PeerJ2018Reading : Set where
  constructor peerj-2018-reading
  field
    soilNutrientsCorrelateWithSOC : Bool
    soilCarbonAndNutrientsIncreaseWithPlantationAge : Bool
    highFoliarDelta15NObserved : Bool
    fixationImportantContributorToPlantationSoilN : Bool
    alternativeSoilNInputsRemainLive : Bool
open PeerJ2018Reading public

canonicalPeerJ2018Reading : PeerJ2018Reading
canonicalPeerJ2018Reading = peerj-2018-reading true true true false true

record Isaac2011Reading : Set where
  constructor isaac-2011-reading
  field
    fixationVariesWithSoilP : Bool
    fixationVariesWithTreeAge : Bool
    higherSoilPAssociatedWithHigherFixation : Bool
    fixationDeclinesWithAgeInStudiedPopulation : Bool
    soilNAndCContextRetained : Bool
open Isaac2011Reading public

canonicalIsaac2011Reading : Isaac2011Reading
canonicalIsaac2011Reading = isaac-2011-reading true true true true true

record PhosphorusExperimentReading : Set where
  constructor phosphorus-experiment-reading
  field
    biomassIncreasesWithP : Bool
    mineralNFromSolutionIncreasesWithP : Bool
    noduleNumberIncreasesWithP : Bool
    atmosphericNDerivedIncreasesWithP : Bool
    nonLimitingNitrogenContextRetained : Bool
open PhosphorusExperimentReading public

canonicalPhosphorusExperimentReading : PhosphorusExperimentReading
canonicalPhosphorusExperimentReading =
  phosphorus-experiment-reading true true false false true

------------------------------------------------------------------------
-- Existing LES owner remains separate.
------------------------------------------------------------------------

drylandWaterCarbonSourceDOI : String
drylandWaterCarbonSourceDOI = Dryland.primaryStudyDOI

drylandBNFJoinedObserverReused : BNFLES.AcaciaBNFLESJoinedObserver
drylandBNFJoinedObserverReused = BNFLES.canonicalJoinedObserver

------------------------------------------------------------------------
-- Finite DASHI factorisation witnesses.
--
-- Four synthetic worlds expose the information-loss shape suggested by the
-- natural-population source: fixation state is context-indexed by both age and
-- edaphic P. They are NOT additional field observations or quantitative
-- reconstructions.
------------------------------------------------------------------------

data EdaphicWorld : Set where
  juvenileHighP : EdaphicWorld
  juvenileLowP : EdaphicWorld
  matureHighP : EdaphicWorld
  matureLowP : EdaphicWorld

data FixationTask : Set where
  realisedFixationTask : FixationTask

treeAgeOnly : EdaphicWorld → Bool
treeAgeOnly juvenileHighP = false
treeAgeOnly juvenileLowP = false
treeAgeOnly matureHighP = true
treeAgeOnly matureLowP = true

soilPOnly : EdaphicWorld → Bool
soilPOnly juvenileHighP = true
soilPOnly juvenileLowP = false
soilPOnly matureHighP = true
soilPOnly matureLowP = false

realisedFixation : FixationTask → EdaphicWorld → Bool
realisedFixation realisedFixationTask juvenileHighP = true
realisedFixation realisedFixationTask juvenileLowP = false
realisedFixation realisedFixationTask matureHighP = false
realisedFixation realisedFixationTask matureLowP = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

treeAgeOnlyNotTaskSufficient :
  LES.TaskFactorisation treeAgeOnly realisedFixation → ⊥
treeAgeOnlyNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor realisedFixationTask {juvenileHighP} {juvenileLowP} refl)

soilPOnlyNotTaskSufficient :
  LES.TaskFactorisation soilPOnly realisedFixation → ⊥
soilPOnlyNotTaskSufficient factor =
  falseNotTrue
    (LES.sameRepresentationSameTaskOutput
      factor realisedFixationTask {juvenileHighP} {matureHighP} refl)

------------------------------------------------------------------------
-- Cross-source phosphorus-context collision.
--
-- One source reports a positive soil-P/fixation association in natural Kenyan
-- populations; the controlled sand-culture source with non-limiting N reports
-- no increase in nodules or atmospheric-N acquisition along its P gradient.
-- DASHI turns that source contrast into an information-loss witness. It is not
-- a claim that the studies are the same population or directly exchangeable.
------------------------------------------------------------------------

data PhosphorusResponseWorld : Set where
  naturalPopulationHigherP : PhosphorusResponseWorld
  nonLimitingNSandCultureHigherP : PhosphorusResponseWorld

data PhosphorusResponseTask : Set where
  atmosphericNResponseTask : PhosphorusResponseTask

higherPOnly : PhosphorusResponseWorld → Bool
higherPOnly _ = true

atmosphericNResponse : PhosphorusResponseTask → PhosphorusResponseWorld → Bool
atmosphericNResponse atmosphericNResponseTask naturalPopulationHigherP = true
atmosphericNResponse atmosphericNResponseTask nonLimitingNSandCultureHigherP = false

higherPAloneNotTaskSufficientAcrossContexts :
  LES.TaskFactorisation higherPOnly atmosphericNResponse → ⊥
higherPAloneNotTaskSufficientAcrossContexts factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor atmosphericNResponseTask
      {naturalPopulationHigherP} {nonLimitingNSandCultureHigherP} refl)

------------------------------------------------------------------------
-- Soil-N mechanism collision.
------------------------------------------------------------------------

data SoilNWorld : Set where
  lowBNFHighOtherN : SoilNWorld
  lowBNFLowOtherN : SoilNWorld

data SoilNTask : Set where
  retainedSoilNTask : SoilNTask

fixationContributionOnly : SoilNWorld → Bool
fixationContributionOnly _ = false

soilNOutcome : SoilNTask → SoilNWorld → Bool
soilNOutcome retainedSoilNTask lowBNFHighOtherN = true
soilNOutcome retainedSoilNTask lowBNFLowOtherN = false

fixationContributionNotTaskSufficientForSoilN :
  LES.TaskFactorisation fixationContributionOnly soilNOutcome → ⊥
fixationContributionNotTaskSufficientForSoilN factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor retainedSoilNTask {lowBNFHighOtherN} {lowBNFLowOtherN} refl)

------------------------------------------------------------------------
-- Repair surface.
------------------------------------------------------------------------

record FixationContextRepair : Set where
  constructor fixation-context-repair
  field
    hostIdentityRetained : Bool
    treeAgeRetained : Bool
    soilPhosphorusRetained : Bool
    nitrogenAvailabilityRegimeRetained : Bool
    siteAndExperimentalSystemRetained : Bool
    isotopeMethodRetained : Bool
    soilCarbonRetained : Bool
    soilNPoolAndFluxRetained : Bool
    alternativeNInputsRetained : Bool
    sourceIdentityRetained : Bool
    measurementObjectRetained : Bool
open FixationContextRepair public

canonicalFixationContextRepair : FixationContextRepair
canonicalFixationContextRepair =
  fixation-context-repair true true true true true true true true true true true

record AcaciaBNFEdaphicBoundary : Set where
  constructor acacia-bnf-edaphic-boundary
  field
    treeAgeAloneAdequateForFixation : Bool
    soilPAloneAdequateForFixation : Bool
    higherPUniversallyIncreasesAtmosphericN : Bool
    higherPUniversallyIncreasesNodules : Bool
    phosphorusResponseIndependentOfNitrogenRegime : Bool
    nitrogenFixingSpeciesLabelCreatesRealisedContribution : Bool
    soilNAccretionIdentifiesBNFContribution : Bool
    highSOCIdentifiesFixationMechanism : Bool
    sameSudanProgrammeCreatesSameMeasurementObject : Bool
    delta15NMeasurementEqualsDirectNitrogenaseRate : Bool
    oneSitePatternCreatesGlobalRule : Bool
    edaphicOntogeneticAndNRegimeContextRetained : Bool
    alternativeNitrogenInputsRetained : Bool
    mergedDrylandLESReusedWithoutSourceFusion : Bool
    syntheticWorldsAreExternalObservations : Bool
open AcaciaBNFEdaphicBoundary public

canonicalEdaphicBoundary : AcaciaBNFEdaphicBoundary
canonicalEdaphicBoundary = acacia-bnf-edaphic-boundary
  false false false false false false false false false false false
  true true true false

attributionRule : String
attributionRule =
  "Abaker et al. PeerJ 2018 (DOI 10.7717/peerj.5232; PMID 30018862; PMCID PMC6044267) owns only its Sudan soil-fertility/delta-15N propositions. Isaac, Harmand, Lesueur & Lelon 2011 (DOI 10.1016/j.foreco.2010.11.011) owns only its Kenya natural-population age/P/fixation and soil-N/C propositions. Isaac, Harmand & Drevon 2011 (DOI 10.1016/j.jplph.2010.10.011; PMID 21211863) owns only its sand-culture P-gradient/non-limiting-N propositions. The merged hydrology source DOI 10.1016/j.jaridenv.2017.12.004 remains a distinct measurement object. DASHI owns the cross-source TaskFactorisation collisions, repair record and no-promotion boundaries; no source is attributed a DASHI factorisation theorem or universal P-response/deployment conclusion."
