module DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact as Science
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- THIN EXTENSION OF THE CANONICAL IBRAHIM / DEWEY / DOI / QID OWNER
--
-- Adds primary South-East-Queensland population/connectivity and offset-model
-- leaves that sharpen the open s 13 population-identity/counterfactual task.
-- No second traversal, attribution, legal-atom or coverage ontology is created.
------------------------------------------------------------------------

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Id.itemId "Q2993449"

landscapeEcologyQid : Id.ItemId
landscapeEcologyQid = Id.itemId "Q738011"

conservationBiologyQid : Id.ItemId
conservationBiologyQid = Id.itemId "Q641498"

southEastQueenslandQid : Id.ItemId
southEastQueenslandQid = Id.itemId "Q1894392"

habitatFragmentationQid : Id.ItemId
habitatFragmentationQid = Id.itemId "Q913302"

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

biologyDewey : String
biologyDewey = "570.000"

koalaDewey : String
koalaDewey = "599.25"

ecologyDewey : String
ecologyDewey = "577"

conservationDewey : String
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Primary empirical population/connectivity sources.
------------------------------------------------------------------------

dudaniec2013 : Source.AttributedSource
dudaniec2013 = Source.mkDOISource
  "Rachael Y. Dudaniec; Jonathan R. Rhodes; Jessica Worthington Wilmer; Mitchell Lyons; Kristen E. Lee; Clive A. McAlpine; Frank N. Carrick"
  "Using multilevel models to identify drivers of landscape-genetic structure among management areas"
  "Molecular Ecology 22(14), 3752-3765"
  "2013"
  "10.1111/mec.12359"
  "https://doi.org/10.1111/mec.12359"
  Source.academicArticleSource
  "Primary empirical South East Queensland landscape-genetics study. It supplies regional evidence that tree cover and roads are associated with koala gene-flow/connectivity structure. It constrains what a defensible local viable-population/connectivity analysis should measure, but it does not identify the present Springview population."
  Source.publicAttribution

lee2010 : Source.AttributedSource
lee2010 = Source.mkDOISource
  "Kristen E. Lee; Jennifer M. Seddon; Sean W. Corley; William A. H. Ellis; Stephen D. Johnston; Deidre L. de Villiers; Harriet J. Preece; Frank N. Carrick"
  "Genetic variation and structuring in the threatened koala populations of Southeast Queensland"
  "Conservation Genetics 11(6), 2091-2103"
  "2010"
  "10.1007/s10592-009-9987-9"
  "https://doi.org/10.1007/s10592-009-9987-9"
  Source.academicArticleSource
  "Primary empirical population-genetics study across Southeast Queensland. It identifies regional genetic structuring and barriers consistent with roads/rivers/urbanisation, and is used to snowball population delimitation questions rather than to assign Springview to a particular genetic cluster without local data."
  Source.publicAttribution

mcalpine2006 : Source.AttributedSource
mcalpine2006 = Source.mkDOISource
  "Clive A. McAlpine; Jonathan R. Rhodes; John G. Callaghan; Michiala E. Bowen; Daniel Lunney; David L. Mitchell; David V. Pullar; Hugh P. Possingham"
  "The importance of forest area and configuration relative to local habitat factors for conserving forest mammals: A case study of koalas in Queensland, Australia"
  "Biological Conservation 132(2), 153-165"
  "2006"
  "10.1016/j.biocon.2006.03.021"
  "https://doi.org/10.1016/j.biocon.2006.03.021"
  Source.academicArticleSource
  "Foundational Queensland empirical landscape study linking koala occurrence to forest area/configuration, road density and local food-tree composition. Used as general mechanism/method evidence for fragmentation and substitutability, never as a Springview occurrence record."
  Source.publicAttribution

brunton2026 : Source.AttributedSource
brunton2026 = Source.mkDOISource
  "Elizabeth A. Brunton; Katrin Hohwieler; Kye McDonald; Romane H. Cristescu"
  "Mapping connectivity for conservation of a threatened iconic mammal, the koala: Trends, challenges and opportunities"
  "Ecological Solutions and Evidence 7(2), e70253"
  "2026"
  "10.1002/2688-8319.70253"
  "https://doi.org/10.1002/2688-8319.70253"
  Source.academicArticleSource
  "Current state-of-the-art review of koala connectivity mapping. It warns against treating structural/potential connectivity maps as realised functional connectivity and identifies limited local-data input and field validation across the reviewed literature."
  Source.publicAttribution

ellisThermal2026 : Source.AttributedSource
ellisThermal2026 = Source.mkDOISource
  "William Anthony Ellis; Madeleine Jennifer Harding; Sean Ian FitzGibbon; Amber Kristen Gillett; Benjamin James Barth"
  "Using thermal drones to validate historical koala surveys"
  "Australian Mammalogy 48(1), AM25037"
  "2026"
  "10.1071/AM25037"
  "https://doi.org/10.1071/AM25037"
  Source.academicArticleSource
  "Recent UQ-led survey-validation study comparing thermal-drone, diurnal and spotlight detection. It is a future method option if existing Ipswich monitoring leaves a decisive local detection/population uncertainty; it does not establish Woogaroo occupancy."
  Source.publicAttribution

sparkes2025 : Source.AttributedSource
sparkes2025 = Source.mkDOISource
  "Gabriella R. Sparkes; Oakleigh Wilson; William A. Ellis; Sean I. FitzGibbon; Benjamin J. Barth; Christofer J. Clemente; Mathew S. Crowther; Robbie S. Wilson"
  "Between the Trees: Quantifying Koala Ground Movement for Conservation Action"
  "Animals 15(24), 3537"
  "2025"
  "10.3390/ani15243537"
  "https://doi.org/10.3390/ani15243537"
  Source.academicArticleSource
  "Recent UQ/USC movement-ecology study quantifying rare but high-risk ground movement between trees in fragmented habitat. Used to sharpen movement/severance and road-interface questions, not to import a site-specific Woogaroo effect size."
  Source.publicAttribution

rhodesOffset2024 : Source.AttributedSource
rhodesOffset2024 = Source.mkDOISource
  "Jonathan R. Rhodes; Yan Liu; Agung Wahyudi; Martine Maron; Md Sayed Iftekhar; Shantala Brisbane"
  "Performance of habitat offsets for species conservation in dynamic human-modified landscapes"
  "People and Nature"
  "2024"
  "10.1002/pan3.10494"
  "https://doi.org/10.1002/pan3.10494"
  Source.academicArticleSource
  "Primary modelling study for South East Queensland koala offsets. It links land-use change, koala abundance and offset regulation and supports a dynamic without-offset/with-offset counterfactual; it does not establish the identity or adequacy of the 2019/8575 offset parcels."
  Source.publicAttribution

seqKoalaOffsetDataset2023 : Source.AttributedSource
seqKoalaOffsetDataset2023 = Source.mkDOISource
  "Jonathan R. Rhodes; Yan Liu; Agung Wahyudi; Martine Maron; Md Sayed Iftekhar; Shantala Brisbane"
  "South East Queensland Koala Offset Analysis"
  "The University of Queensland Research Data"
  "2023"
  "10.48610/1c1164e"
  "https://doi.org/10.48610/1c1164e"
  (Source.namedSourceKind "research dataset")
  "Primary data package for the South East Queensland integrated koala offset analysis. It is an implementation/calibration source for later spatial/LES counterfactual work, not a project-specific legal or ecological conclusion."
  Source.publicAttribution

regionalPopulationSourceAtlas : Source.AttributedSourceAtlas
regionalPopulationSourceAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim population/connectivity source extension"
  "DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact"
  (dudaniec2013 ∷ lee2010 ∷ mcalpine2006 ∷ brunton2026 ∷ ellisThermal2026 ∷ sparkes2025 ∷ rhodesOffset2024 ∷ seqKoalaOffsetDataset2023 ∷ [])
  "Primary South East Queensland population/connectivity and offset-model sources plus current SOTA/method sources. DOI/QID/Dewey coordinates are traversal aids only. Independent literature/data carriers are not independent observations of Springview/Woogaroo without a same-object local join."

------------------------------------------------------------------------
-- Ibrahim coordinates: explicit Dewey/DOI/QID coordinates.
------------------------------------------------------------------------

dudaniecCoordinate : Ibrahim.DashiKnowledgeCoordinate
dudaniecCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala landscape-genetic structure / gene-flow drivers"
  ecologyDewey
  (Id.rawItemId ecologicalConnectivityQid)
  "doi:10.1111/mec.12359"

leeCoordinate : Ibrahim.DashiKnowledgeCoordinate
leeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala population genetic structure"
  koalaDewey
  (Id.rawItemId southEastQueenslandQid)
  "doi:10.1007/s10592-009-9987-9"

mcalpineCoordinate : Ibrahim.DashiKnowledgeCoordinate
mcalpineCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "Queensland koala forest configuration / occurrence"
  ecologyDewey
  (Id.rawItemId landscapeEcologyQid)
  "doi:10.1016/j.biocon.2006.03.021"

bruntonCoordinate : Ibrahim.DashiKnowledgeCoordinate
bruntonCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "koala connectivity mapping state of the art"
  conservationDewey
  (Id.rawItemId ecologicalConnectivityQid)
  "doi:10.1002/2688-8319.70253"

ellisThermalCoordinate : Ibrahim.DashiKnowledgeCoordinate
ellisThermalCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "thermal-drone validation of koala surveys"
  koalaDewey
  (Id.rawItemId koalaQid)
  "doi:10.1071/AM25037"

sparkesMovementCoordinate : Ibrahim.DashiKnowledgeCoordinate
sparkesMovementCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "koala ground movement / fragmented landscape risk"
  koalaDewey
  (Id.rawItemId koalaQid)
  "doi:10.3390/ani15243537"

offsetModelCoordinate : Ibrahim.DashiKnowledgeCoordinate
offsetModelCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala dynamic offset / land-use counterfactual"
  conservationDewey
  (Id.rawItemId koalaQid)
  "doi:10.1002/pan3.10494"

offsetDatasetCoordinate : Ibrahim.DashiKnowledgeCoordinate
offsetDatasetCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala offset analysis dataset"
  conservationDewey
  (Id.rawItemId southEastQueenslandQid)
  "doi:10.48610/1c1164e"

------------------------------------------------------------------------
-- Edge semantics: literature/method support is not a same-object dependency.
------------------------------------------------------------------------

dudaniecToS13 : Ibrahim.DashiFirstLinkEdge
dudaniecToS13 = Ibrahim.dashi-first-link-edge
  dudaniecCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Regional landscape-genetics evidence sharpens the population/connectivity variables an s 13 expert should test. It does not identify the Springview population or prove essentiality."
  true

leeToS13 : Ibrahim.DashiFirstLinkEdge
leeToS13 = Ibrahim.dashi-first-link-edge
  leeCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Regional population structure constrains plausible population boundaries and barriers, but requires a local/current join before it can support the exact s 13 population identity."
  true

mcalpineToS13 : Ibrahim.DashiFirstLinkEdge
mcalpineToS13 = Ibrahim.dashi-first-link-edge
  mcalpineCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Forest area/configuration and road effects provide a tested Queensland mechanism for the without-site/connectivity counterfactual, not a Springview population identity."
  true

bruntonToS13 : Ibrahim.DashiFirstLinkEdge
bruntonToS13 = Ibrahim.dashi-first-link-edge
  bruntonCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The 2026 SOTA review requires us to separate mapped structural/potential connectivity from realised functional connectivity and to prefer local population inputs/field validation."
  true

sparkesToS102 : Ibrahim.DashiFirstLinkEdge
sparkesToS102 = Ibrahim.dashi-first-link-edge
  sparkesMovementCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Fine-scale movement evidence sharpens the causal question whether severance increases risky between-tree ground movement/road-interface exposure; it is not a Woogaroo effect measurement."
  true

ellisThermalToS13 : Ibrahim.DashiFirstLinkEdge
ellisThermalToS13 = Ibrahim.dashi-first-link-edge
  ellisThermalCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Thermal-drone validation is a fallback acquisition method if the existing Ipswich longitudinal monitoring cannot resolve a material current-population question."
  true

offsetModelToFederal : Ibrahim.DashiFirstLinkEdge
offsetModelToFederal = Ibrahim.dashi-first-link-edge
  offsetModelCoordinate Canonical.projectEcologyCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Dynamic offset modelling supplies counterfactual method for impact/offset analysis, not a finding about the final 2019/8575 offset sites."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record RegionalSourceAtomBinding : Set where
  constructor regional-source-atom-binding
  field
    coordinate : Ibrahim.DashiKnowledgeCoordinate
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    methodPaid : Bool
    sameObjectPaid : Bool
    acquisitionUse : String
    noPromotionBoundary : String

open RegionalSourceAtomBinding public

dudaniecPopulationBinding : RegionalSourceAtomBinding
dudaniecPopulationBinding = regional-source-atom-binding
  dudaniecCoordinate Atom.habitatPopulationEssentialityAtom Atom.nca13EssentialityConsumer
  true false
  "Use tree cover, road barriers and realised genetic connectivity as candidate variables when defining the relevant viable population and testing whether Springview functions as a bottleneck or replaceable patch."
  "Regional gene-flow evidence does not identify a Springview population or satisfy s 13."

leePopulationBinding : RegionalSourceAtomBinding
leePopulationBinding = regional-source-atom-binding
  leeCoordinate Atom.habitatPopulationEssentialityAtom Atom.nca13EssentialityConsumer
  true false
  "Use regional genetic structuring as a prior for acquisition: locate current local genetics, telemetry, density or repeated occurrence evidence that can place Springview/Woogaroo within a defensible population unit."
  "Historical regional clusters are not automatically current local population boundaries."

mcalpineEssentialityBinding : RegionalSourceAtomBinding
mcalpineEssentialityBinding = regional-source-atom-binding
  mcalpineCoordinate Atom.habitatPopulationEssentialityAtom Atom.nca13EssentialityConsumer
  true false
  "Use forest area, configuration, road density and food-tree composition as scientifically grounded variables in the without-site and substitutability analysis."
  "General Queensland landscape relationships do not themselves make this parcel essential."

bruntonConnectivityBinding : RegionalSourceAtomBinding
bruntonConnectivityBinding = regional-source-atom-binding
  bruntonCoordinate Atom.habitatPopulationEssentialityAtom Atom.nca13EssentialityConsumer
  true false
  "Require explicit classification of each connectivity product as structural, potential functional or realised functional; demand local validation where the conclusion depends on function rather than map adjacency."
  "A corridor map is not realised functional connectivity and cannot alone pay s 13 essentiality."

sparkesEffectBinding : RegionalSourceAtomBinding
sparkesEffectBinding = regional-source-atom-binding
  sparkesMovementCoordinate Atom.likelySignificantDetrimentalEffectAtom Atom.nca102InterimOrderConsumer
  true false
  "Use the movement study to frame a testable mechanism: habitat severance can force risky ground movement between trees and increase exposure at fragmented interfaces."
  "General movement mechanism is not a measured Springview effect or a Ministerial s 102 opinion."

ellisDetectionBinding : RegionalSourceAtomBinding
ellisDetectionBinding = regional-source-atom-binding
  ellisThermalCoordinate Atom.affectedWildlifeHabitatAtom Atom.nca102InterimOrderConsumer
  true false
  "If local monitoring remains ambiguous, use thermal-drone survey as a candidate independent detection method with explicit detection-performance provenance."
  "Method validation elsewhere does not prove local occupancy or abundance."

offsetRiskBinding : RegionalSourceAtomBinding
offsetRiskBinding = regional-source-atom-binding
  offsetModelCoordinate Atom.offsetBaselineRiskOfLossAtom Atom.epbc8575OffsetAdequacyConsumer
  true false
  "Use the dynamic land-use/abundance framework after exact final offset parcels and current protection states are identified."
  "A regional model cannot manufacture parcel identity, baseline loss risk or additionality."

offsetLagBinding : RegionalSourceAtomBinding
offsetLagBinding = regional-source-atom-binding
  offsetDatasetCoordinate Atom.offsetRestorationLagAtom Atom.epbc8575OffsetAdequacyConsumer
  true false
  "Use the UQ input data and model lineage to calibrate later restoration-lag and habitat-substitution analysis where compatible."
  "Dataset availability is not proof of project-specific restoration performance or functional equivalence."

------------------------------------------------------------------------
-- Acquisition result: literature Snowball is now sufficiently deep; same-
-- object work remains the highest-alpha next step.
------------------------------------------------------------------------

record PopulationSnowballState : Set where
  constructor population-snowball-state
  field
    regionalGeneticStructureSourcePaid : Bool
    regionalLandscapeGeneticSourcePaid : Bool
    foundationalLandscapeStudyPaid : Bool
    sotaConnectivityReviewPaid : Bool
    thermalDetectionMethodPaid : Bool
    groundMovementMethodPaid : Bool
    rangeWideGenomicsAlreadyCanonical : Bool
    dynamicOffsetModelPaid : Bool
    offsetDatasetPaid : Bool
    localPopulationIdentityPaid : Bool
    localFunctionalConnectivityPaid : Bool
    localWithoutSiteCounterfactualPaid : Bool
    nextAction : String

currentPopulationSnowballState : PopulationSnowballState
currentPopulationSnowballState = population-snowball-state
  true true true true true true true true true
  false false false
  "Use existing Ipswich/Biolink/IKPS local monitoring first. The 2026 SOTA review says koala connectivity studies often lack local inputs and direct validation; therefore stop accumulating generic literature and acquire the local repeated-monitoring/rescue carriers needed to identify the population and validate function. Escalate to new thermal/telemetry/genetic work only for a surviving consumer residual."

------------------------------------------------------------------------
-- Canonical owners remain authoritative.
------------------------------------------------------------------------

canonicalIbrahimCoverage : Canonical.WoogarooIbrahimCoverage
canonicalIbrahimCoverage = Canonical.currentWoogarooIbrahimCoverage

canonicalScienceState : Science.ConsumerScienceState
canonicalScienceState = Science.currentConsumerScienceState

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data RegionalPopulationStudyEqualsLocalPopulationIdentity : Set where
data HistoricalGeneticClusterEqualsCurrentViablePopulation : Set where
data DoiQidDeweyEqualsEvidencePayment : Set where
data OffsetModelEqualsOffsetParcelFact : Set where
data DatasetEqualsLegalConclusion : Set where
data StructuralConnectivityEqualsRealisedFunctionalConnectivity : Set where
data ThermalMethodEqualsLocalDetection : Set where
data GroundMovementMechanismEqualsLocalEffect : Set where

regionalStudyDoesNotIdentifyLocalPopulation : RegionalPopulationStudyEqualsLocalPopulationIdentity → ⊥
regionalStudyDoesNotIdentifyLocalPopulation ()

historicalClusterDoesNotBecomeCurrentPopulation : HistoricalGeneticClusterEqualsCurrentViablePopulation → ⊥
historicalClusterDoesNotBecomeCurrentPopulation ()

coordinatesDoNotPayEvidence : DoiQidDeweyEqualsEvidencePayment → ⊥
coordinatesDoNotPayEvidence ()

offsetModelDoesNotCreateParcelFact : OffsetModelEqualsOffsetParcelFact → ⊥
offsetModelDoesNotCreateParcelFact ()

datasetDoesNotCreateLegalConclusion : DatasetEqualsLegalConclusion → ⊥
datasetDoesNotCreateLegalConclusion ()

structuralMapDoesNotBecomeRealisedConnectivity : StructuralConnectivityEqualsRealisedFunctionalConnectivity → ⊥
structuralMapDoesNotBecomeRealisedConnectivity ()

thermalMethodDoesNotCreateLocalDetection : ThermalMethodEqualsLocalDetection → ⊥
thermalMethodDoesNotCreateLocalDetection ()

groundMovementDoesNotCreateLocalEffect : GroundMovementMechanismEqualsLocalEffect → ⊥
groundMovementDoesNotCreateLocalEffect ()
