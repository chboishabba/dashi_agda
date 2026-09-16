module DASHI.Law.SensibLawWoogarooIbrahimPopulationValidationSotaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring
import DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact as Population
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- IBRAHIM FOLLOW: POPULATION VALIDATION / MONITORING SOTA
--
-- Thin extension of the existing Ibrahim/Dewey/DOI/QID/legal-atom lane.
-- It does not create a new source or legal ontology.  It adds current and
-- locally relevant validation producers, keeps primary report identity
-- separate from web host identity, and routes each source only to the legal
-- atom it can actually inform.
------------------------------------------------------------------------

data ValidationSourceRole : Set where
  primaryLocalGovernmentMonitoring : ValidationSourceRole
  primaryRegionalFieldGenetics : ValidationSourceRole
  primaryNationalMonitoringProgram : ValidationSourceRole
  primaryPeerReviewedGenomicMethod : ValidationSourceRole

data ValidationLocality : Set where
  ipswichLocal : ValidationLocality
  brisbaneSeqRegional : ValidationLocality
  nationalMethod : ValidationLocality
  distributionWideMethod : ValidationLocality

data ValidationUse : Set where
  populationIdentity : ValidationUse
  functionalConnectivity : ValidationUse
  currentOccupancy : ValidationUse
  movementRisk : ValidationUse
  methodCalibration : ValidationUse

koalaQid : Id.ItemId
koalaQid = Canonical.koalaQid

populationGeneticsQid : Id.ItemId
populationGeneticsQid = Canonical.populationGeneticsQid

geneFlowQid : Id.ItemId
geneFlowQid = Canonical.geneFlowQid

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Canonical.ecologicalConnectivityQid

koalaDewey : String
koalaDewey = Canonical.koalaDewey

populationGeneticsDewey : String
populationGeneticsDewey = Canonical.populationGeneticsDewey

ecologyDewey : String
ecologyDewey = "577"

conservationDewey : String
conservationDewey = Canonical.conservationDewey

------------------------------------------------------------------------
-- Attributed sources.
------------------------------------------------------------------------

ipswichBiodiversity2016FullBody : Source.AttributedSource
ipswichBiodiversity2016FullBody = Source.mkNoDOISource
  "Teresa J. Eyre; Dan Ferguson; Annie L. Kelly; Jian Wang; M. Venz"
  "Ipswich City Council Biodiversity Monitoring Project — Final Report"
  "Queensland Herbarium, Department of Science, Information Technology and Innovation"
  "2016"
  "https://www.researchgate.net/publication/326494130_Ipswich_City_Council_Biodiversity_Monitoring_Project_Final_Report"
  (Source.namedSourceKind "government technical monitoring report — full report body available via non-authoritative mirror")
  "Primary Queensland Herbarium monitoring report. The accessible report body records permanent and targeted biodiversity monitoring across Ipswich reserves and reports Koala detections including White Rock-Spring Mountain. The ResearchGate URL is a distribution mirror, not the issuing authority; report authorship/institution and host identity remain separate."
  Source.publicAttribution

owadBrisbane2018 : Source.AttributedSource
owadBrisbane2018 = Source.mkNoDOISource
  "Olivia Woosnam; Faye Wedrowicz"
  "2018 Koala Detection Dog Survey Report"
  "OWAD Environment with WildDNA / Federation University Australia, prepared for Brisbane City Council; Version 2 dated 3 September 2019"
  "2019"
  "https://biocollect.ala.org.au/document/download/2019-10/Koala%20Detection%20Dog%20report%20round%202%202018.pdf"
  (Source.namedSourceKind "primary consultant field/genetics monitoring report")
  "Primary regional field/genetics report using detection dogs, scat genetics and population-structure analysis across Brisbane and surrounds. It includes regional population-structure and migration analyses and describes fragmentation-related loss of links near Greenbank/White Rock-Spring Mountain as relevant to low observed activity in one surveyed group. It is not a Springview same-object effect measurement."
  Source.publicAttribution

nationalKoalaMonitoring2025 : Source.AttributedSource
nationalKoalaMonitoring2025 = Source.mkNoDOISource
  "Australian Government Department of Climate Change, Energy, the Environment and Water"
  "National Koala Monitoring Program — 2025 koala population estimate"
  "DCCEEW National Koala Monitoring Program"
  "2025"
  "https://www.dcceew.gov.au/environment/biodiversity/threatened/species/koalas/national-koala-monitoring-program"
  Source.governmentSource
  "Primary national monitoring-program source. It reports the 2025 listed-population estimate and expressly explains that the increase from earlier estimates largely reflects increased survey effort and better information. Used as monitoring/model-calibration context only, not evidence that the local Woogaroo population increased."
  Source.publicAttribution

donnellyEtAl2025 : Source.AttributedSource
donnellyEtAl2025 = Source.mkDOISource
  "Lily F. Donnelly; Shannon R. Kjeldsen; Matthew J. Lott; Kellie Leigh; Matthew A. Field; Ira R. Cooke; Belinda R. Wright; Kyall R. Zenger"
  "Development and Validation of a Standardised Genomic Tool for Conservation Management of the Koala (Phascolarctos cinereus)"
  "Animals 15(23), 3375"
  "2025"
  "10.3390/ani15233375"
  "https://doi.org/10.3390/ani15233375"
  Source.academicArticleSource
  "Primary peer-reviewed method paper validating a standardised SNP assay for population diversity/differentiation, provenance, parentage and pathogen screening from multiple sample types. It supplies a practical future population-identification method if existing local monitoring cannot resolve the s 13 population bridge; it does not itself identify the Woogaroo population."
  Source.publicAttribution

populationValidationAtlas : Source.AttributedSourceAtlas
populationValidationAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim population-validation SOTA extension"
  "DASHI.Law.SensibLawWoogarooIbrahimPopulationValidationSotaExact"
  (ipswichBiodiversity2016FullBody ∷ owadBrisbane2018 ∷ nationalKoalaMonitoring2025 ∷ donnellyEtAl2025 ∷ [])
  "Primary local/regional monitoring, primary national monitoring and peer-reviewed genomics method. DOI/QID/Dewey coordinates identify and navigate sources; they do not create same-object identity, ecological effect, essentiality or legal satisfaction. Mirror-host identity does not replace issuer identity."

------------------------------------------------------------------------
-- Ibrahim knowledge coordinates.
------------------------------------------------------------------------

ipswich2016Coordinate : Ibrahim.DashiKnowledgeCoordinate
ipswich2016Coordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationValidationSotaExact.agda"
  "Ipswich reserve biodiversity monitoring / local Koala detections"
  koalaDewey
  (Id.rawItemId koalaQid)
  "Queensland Herbarium 2016 report; no DOI; paper/report QID unresolved"

owadGeneticsCoordinate : Ibrahim.DashiKnowledgeCoordinate
owadGeneticsCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationValidationSotaExact.agda"
  "SEQ detection-dog scat genetics / regional Koala population structure"
  populationGeneticsDewey
  (Id.rawItemId populationGeneticsQid)
  "OWAD/WildDNA report Version 2 (2019); no DOI; report QID unresolved"

nkmpCoordinate : Ibrahim.DashiKnowledgeCoordinate
nkmpCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationValidationSotaExact.agda"
  "National Koala Monitoring Program / survey-model calibration"
  conservationDewey
  (Id.rawItemId koalaQid)
  "DCCEEW NKMP; no DOI; program QID unresolved"

genomicAssayCoordinate : Ibrahim.DashiKnowledgeCoordinate
genomicAssayCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationValidationSotaExact.agda"
  "standardised koala SNP assay / population differentiation and provenance"
  populationGeneticsDewey
  (Id.rawItemId populationGeneticsQid)
  "doi:10.3390/ani15233375; paper QID unresolved"

------------------------------------------------------------------------
-- Snowball edges into live legal consumers.
------------------------------------------------------------------------

ipswich2016ToS13 : Ibrahim.DashiFirstLinkEdge
ipswich2016ToS13 = Ibrahim.dashi-first-link-edge
  ipswich2016Coordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Independent local monitoring establishes historical Koala detections within the adjacent Ipswich conservation-estate network and provides a dated baseline. It does not identify the current Springview viable population or prove essentiality."
  true

owadToS13 : Ibrahim.DashiFirstLinkEdge
owadToS13 = Ibrahim.dashi-first-link-edge
  owadGeneticsCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Regional scat-genetic population structure shows a feasible non-invasive route from local samples to empirical population/gene-flow structure. Regional clusters are not automatically the Woogaroo population."
  true

owadToS102 : Ibrahim.DashiFirstLinkEdge
owadToS102 = Ibrahim.dashi-first-link-edge
  owadGeneticsCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Regional field evidence makes fragmentation, link loss and movement/population isolation empirically testable pathways for an s 102 expert. It does not supply the Springview likelihood/effect conclusion."
  true

nkmpToS13Method : Ibrahim.DashiFirstLinkEdge
nkmpToS13Method = Ibrahim.dashi-first-link-edge
  nkmpCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "National monitoring demonstrates why estimate changes must be separated from biological population change and why local survey effort/model inputs need explicit receipts."
  true

genomicAssayToS13 : Ibrahim.DashiFirstLinkEdge
genomicAssayToS13 = Ibrahim.dashi-first-link-edge
  genomicAssayCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The validated assay is a future producer for population differentiation/provenance if local monitoring leaves the population-identity atom unresolved. It is not first-line evidence while existing Ipswich longitudinal data remain unacquired."
  true

------------------------------------------------------------------------
-- Legal-atom intersection.
------------------------------------------------------------------------

record ValidationAtomBinding : Set where
  constructor validation-atom-binding
  field
    coordinate : Ibrahim.DashiKnowledgeCoordinate
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    role : ValidationSourceRole
    locality : ValidationLocality
    use : ValidationUse
    admissible : Bool
    sameObjectPaid : Bool
    atomComplete : Bool
    contribution : String
    residual : String

open ValidationAtomBinding public

ipswich2016PopulationBinding : ValidationAtomBinding
ipswich2016PopulationBinding = validation-atom-binding
  ipswich2016Coordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryLocalGovernmentMonitoring ipswichLocal currentOccupancy
  true false false
  "Pays an independent historical local monitoring baseline, including a White Rock-Spring Mountain Koala detection within the Ipswich reserve network."
  "Springview same-object population identity, current occupancy/connectivity and the without-site essentiality counterfactual remain open."

owadPopulationBinding : ValidationAtomBinding
owadPopulationBinding = validation-atom-binding
  owadGeneticsCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryRegionalFieldGenetics brisbaneSeqRegional populationIdentity
  true false false
  "Pays a tested non-invasive regional population/genetics producer family and empirical regional population-structure context."
  "Do not import Brisbane genetic clusters or migration rates into Woogaroo; local samples or appropriately joined local monitoring are required."

owadEffectBinding : ValidationAtomBinding
owadEffectBinding = validation-atom-binding
  owadGeneticsCoordinate
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  primaryRegionalFieldGenetics brisbaneSeqRegional movementRisk
  true false false
  "Supports a concrete regional fragmentation/isolation pathway and identifies field/genetic measures that can test movement/population effects."
  "The approved 9281 process still needs current same-object ecological opinion and mitigation-adjusted likely-effect analysis."

nkmpPopulationBinding : ValidationAtomBinding
nkmpPopulationBinding = validation-atom-binding
  nkmpCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryNationalMonitoringProgram nationalMethod methodCalibration
  true false false
  "Calibrates interpretation of population estimates: changed survey coverage/model information can change estimates without equivalent biological population growth."
  "National estimates do not identify the local viable population or its dependence on Springview habitat."

genomicAssayPopulationBinding : ValidationAtomBinding
genomicAssayPopulationBinding = validation-atom-binding
  genomicAssayCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryPeerReviewedGenomicMethod distributionWideMethod populationIdentity
  true false false
  "Provides a current validated producer for differentiation/provenance if a local genetic question survives existing-data acquisition."
  "No Woogaroo samples have been typed through this assay; method availability is not local population evidence."

------------------------------------------------------------------------
-- Consumer-oriented acquisition ladder.
------------------------------------------------------------------------

record PopulationValidationLadder : Set where
  constructor population-validation-ladder
  field
    first : String
    second : String
    third : String
    fourth : String
    existingDataBeforeNewGenomics : Bool
    nationalEstimateNotLocalTrend : Bool
    mirrorNotIssuer : Bool
    currentS13Paid : Bool
    currentS102Paid : Bool

currentPopulationValidationLadder : PopulationValidationLadder
currentPopulationValidationLadder = population-validation-ladder
  "Acquire the actual Ipswich 2020, 2023 and 2025 Biolink monitoring reports/data, especially White Rock-Spring Mountain site results, coordinates/IDs, occupancy/activity trends and any metapopulation interpretation."
  "Acquire locality-appropriate IKPS/QWildlife/rescue/mortality/sighting records and any Council Springfield fauna-management monitoring that can join current animals and threats to the Woogaroo/Opossum landscape."
  "If the viable-population boundary or realised connectivity remains material and unresolved, obtain targeted contemporary field validation (e.g. scat/detection survey or telemetry as appropriate)."
  "Only if the population-identity consumer still survives, consider non-invasive genomics using a validated population-differentiation/provenance method such as Donnelly et al. 2025, with explicit sampling design and expert interpretation."
  true true true false false

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data ResearchGateMirrorEqualsIssuer : Set where
data HistoricalWhiteRockDetectionEqualsSpringviewCurrentOccupancy : Set where
data BrisbaneGeneticClusterEqualsWoogarooPopulation : Set where
data NationalEstimateIncreaseEqualsLocalPopulationIncrease : Set where
data ValidatedGenomicToolEqualsWoogarooPopulationIdentified : Set where
data MoreSourcesEqualsAtomPaid : Set where

mirrorDoesNotBecomeIssuer : ResearchGateMirrorEqualsIssuer → ⊥
mirrorDoesNotBecomeIssuer ()

historicalDetectionDoesNotBecomeCurrentSpringviewOccupancy : HistoricalWhiteRockDetectionEqualsSpringviewCurrentOccupancy → ⊥
historicalDetectionDoesNotBecomeCurrentSpringviewOccupancy ()

regionalClusterDoesNotBecomeLocalPopulation : BrisbaneGeneticClusterEqualsWoogarooPopulation → ⊥
regionalClusterDoesNotBecomeLocalPopulation ()

nationalEstimateDoesNotBecomeLocalTrend : NationalEstimateIncreaseEqualsLocalPopulationIncrease → ⊥
nationalEstimateDoesNotBecomeLocalTrend ()

genomicMethodDoesNotIdentifyPopulationWithoutSamples : ValidatedGenomicToolEqualsWoogarooPopulationIdentified → ⊥
genomicMethodDoesNotIdentifyPopulationWithoutSamples ()

citationGrowthDoesNotPayAtom : MoreSourcesEqualsAtomPaid → ⊥
citationGrowthDoesNotPayAtom ()

------------------------------------------------------------------------
-- Explicit continuation of the existing monitoring lane.
------------------------------------------------------------------------

existingMonitoringFrontier : Monitoring.ExistingMonitoringFrontier
existingMonitoringFrontier = Monitoring.currentExistingMonitoringFrontier

regionalPopulationAtlas : Source.AttributedSourceAtlas
regionalPopulationAtlas = Population.regionalPopulationSourceAtlas
