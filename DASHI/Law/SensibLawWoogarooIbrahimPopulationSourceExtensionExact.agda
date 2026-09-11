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

southEastQueenslandQid : Id.ItemId
southEastQueenslandQid = Id.itemId "Q1894392"

habitatFragmentationQid : Id.ItemId
habitatFragmentationQid = Id.itemId "Q913302"

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

biologyDewey : String
biologyDewey = "570.000"

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
  (dudaniec2013 ∷ lee2010 ∷ rhodesOffset2024 ∷ seqKoalaOffsetDataset2023 ∷ [])
  "Primary South East Queensland population/connectivity and offset-model sources. These are independent literature/data carriers but not independent observations of Springview/Woogaroo; same-object local payment remains separate."

------------------------------------------------------------------------
-- Ibrahim coordinates: broad repo-native Dewey parent, explicit DOI/QID.
------------------------------------------------------------------------

dudaniecCoordinate : Ibrahim.DashiKnowledgeCoordinate
dudaniecCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala landscape-genetic structure / gene-flow drivers"
  biologyDewey
  (Id.rawItemId ecologicalConnectivityQid)
  "doi:10.1111/mec.12359"

leeCoordinate : Ibrahim.DashiKnowledgeCoordinate
leeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala population genetic structure"
  biologyDewey
  (Id.rawItemId southEastQueenslandQid)
  "doi:10.1007/s10592-009-9987-9"

offsetModelCoordinate : Ibrahim.DashiKnowledgeCoordinate
offsetModelCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala dynamic offset / land-use counterfactual"
  biologyDewey
  (Id.rawItemId koalaQid)
  "doi:10.1002/pan3.10494"

offsetDatasetCoordinate : Ibrahim.DashiKnowledgeCoordinate
offsetDatasetCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimPopulationSourceExtensionExact.agda"
  "SEQ koala offset analysis dataset"
  biologyDewey
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
    sotaConnectivityReviewAlreadyCanonical : Bool
    rangeWideGenomicsAlreadyCanonical : Bool
    dynamicOffsetModelPaid : Bool
    offsetDatasetPaid : Bool
    localPopulationIdentityPaid : Bool
    localFunctionalConnectivityPaid : Bool
    localWithoutSiteCounterfactualPaid : Bool
    nextAction : String

currentPopulationSnowballState : PopulationSnowballState
currentPopulationSnowballState = population-snowball-state
  true true true true true true
  false false false
  "Stop accumulating generic literature for its own sake. Acquire/commission current local population, movement/connectivity and expert-effect evidence; use the DOI/QID/Dewey graph to select and calibrate methods, not to substitute for the same-object join."

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
