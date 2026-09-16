module DASHI.Law.SensibLawWoogarooIbrahimLocalPopulationEvidenceExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact as Regional
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- LOCAL POPULATION EVIDENCE EXTENSION
--
-- Adds primary/regional population sources that sharpen the s 13
-- population-identity question. This extends the existing Ibrahim/Snowball
-- graph; it does not create another traversal or legal ontology.
------------------------------------------------------------------------

data LocalPopulationSourceRole : Set where
  primaryResearchReport
  primaryLocalGovernmentPlan
  primaryRegionalPopulationStudy : LocalPopulationSourceRole

data LocalPopulationRelation : Set where
  ipswichWide
  whiteRockSpringMountainAdjacent
  regionalGeneticContext
  exactSpringviewUnresolved : LocalPopulationRelation

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

southEastQueenslandQid : Id.ItemId
southEastQueenslandQid = Id.itemId "Q1894392"

wildlifeCorridorQid : Id.ItemId
wildlifeCorridorQid = Id.itemId "Q864912"

populationGeneticsQid : Id.ItemId
populationGeneticsQid = Id.itemId "Q31151"

koalaDewey ecologyDewey conservationDewey populationGeneticsDewey : String
koalaDewey = "599.25"
ecologyDewey = "577"
conservationDewey = "333.95"
populationGeneticsDewey = "576.58"

------------------------------------------------------------------------
-- Located sources.
------------------------------------------------------------------------

busseyEllis2016 : Source.AttributedSource
busseyEllis2016 = Source.mkNoDOISource
  "Joanne Bussey; Bill Ellis"
  "The koalas of Ipswich: Opportunities, threats and future viability"
  "School of Agriculture and Food Sciences, The University of Queensland; prepared for Lock the Gate Alliance"
  "2016"
  "https://d3n8a8pro7vhmx.cloudfront.net/lockthegate/pages/2624/attachments/original/1456354727/3299_LOCK_THE_GATE_KOALA_REPORT-9V_SCREEN.pdf"
  (Source.namedSourceKind "research report")
  "Primary authored Ipswich-wide synthesis used by Ipswich City Council's Koala Conservation and Habitat Management Plan. It addresses local population size/distribution, threats, connectivity and future viability. Used as local-population context, not as exact Springview population identity without a spatial/genetic join."
  Source.publicAttribution

ipswichKoalaPlan : Source.AttributedSource
ipswichKoalaPlan = Source.mkNoDOISource
  "Ipswich City Council"
  "Koala Conservation and Habitat Management Plan"
  "Ipswich City Council"
  "2016, current public copy"
  "https://www.ipswich.qld.gov.au/files/assets/public/v/1/about-council/initiatives/environment/wildlife/koala-conservation/documents/koala-conservation-plan.pdf"
  Source.governmentSource
  "Primary local-government conservation plan. It identifies White Rock-Spring Mountain as a Core Habitat Area, describes its native vegetation as a critical habitat link in the Flinders-Karawatha corridor, and identifies Springfield-side urban development as a future threat. It also cites Bussey and Ellis 2016 and Lee et al. 2010 for Ipswich population/genetic context."
  Source.publicAttribution

scenicRim2024 : Source.AttributedSource
scenicRim2024 = Source.mkDOISource
  "Olivia Woosnam; Fiona E. Hogan"
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council / OWAD Environment / WildDNA / Federation University technical report"
  "2025"
  "10.13140/RG.2.2.24954.20163"
  "https://www.scenicrim.qld.gov.au/files/assets/public/v/1/our-environment/biodiversity/koalas/documents/scenicrim_2024koalastudyreport_final.pdf"
  (Source.namedSourceKind "primary regional genetic population study")
  "Primary government-hosted regional genetic study using Koala genotypes and spatial clustering. It identifies five population clusters within the Scenic Rim study area and asymmetric migration toward the cluster labelled SEQ-03. It does not by itself establish that SEQ-03 is the same label as SEQ West, nor genetically assign Springview/Woogaroo."
  Source.publicAttribution

localPopulationAtlas : Source.AttributedSourceAtlas
localPopulationAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim local population evidence extension"
  "DASHI.Law.SensibLawWoogarooIbrahimLocalPopulationEvidenceExtensionExact"
  (busseyEllis2016 ∷ ipswichKoalaPlan ∷ scenicRim2024 ∷ [])
  "Local/regional population and corridor sources. Report authorship, DOI state, institutional source, geographic scope and source role are explicit. No source is promoted into an exact Springview viable-population identity without a same-object spatial/genetic join."

------------------------------------------------------------------------
-- Ibrahim Dewey / QID / source coordinates.
------------------------------------------------------------------------

busseyEllisCoordinate : Ibrahim.DashiKnowledgeCoordinate
busseyEllisCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimLocalPopulationEvidenceExtensionExact.agda"
  "Ipswich koala opportunities, threats and future viability"
  koalaDewey
  (Id.rawItemId cityOfIpswichQid)
  "Bussey & Ellis 2016 UQ research report; no DOI located"

whiteRockCoreHabitatCoordinate : Ibrahim.DashiKnowledgeCoordinate
whiteRockCoreHabitatCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimLocalPopulationEvidenceExtensionExact.agda"
  "White Rock-Spring Mountain Core Habitat Area / Flinders-Karawatha link"
  conservationDewey
  (Id.rawItemId wildlifeCorridorQid)
  "Ipswich City Council Koala Conservation and Habitat Management Plan"

seq03GeneticCoordinate : Ibrahim.DashiKnowledgeCoordinate
seq03GeneticCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimLocalPopulationEvidenceExtensionExact.agda"
  "SEQ-03 Scenic Rim genetic cluster / migration topology"
  populationGeneticsDewey
  (Id.rawItemId populationGeneticsQid)
  "doi:10.13140/RG.2.2.24954.20163; primary: Scenic Rim Regional Council hosted report"

busseyToS13 : Ibrahim.DashiFirstLinkEdge
busseyToS13 = Ibrahim.dashi-first-link-edge
  busseyEllisCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Ipswich-wide viability work narrows the relevant population context but does not identify Springview's exact viable population."
  true

whiteRockToS13 : Ibrahim.DashiFirstLinkEdge
whiteRockToS13 = Ibrahim.dashi-first-link-edge
  whiteRockCoreHabitatCoordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Council identifies the adjacent White Rock-Spring Mountain estate as a Core Habitat Area and Flinders-Karawatha habitat link; this strengthens the landscape-function question but does not itself prove Springview habitat essentiality."
  true

seq03ToS13 : Ibrahim.DashiFirstLinkEdge
seq03ToS13 = Ibrahim.dashi-first-link-edge
  seq03GeneticCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Regional genetic evidence identifies differentiated Scenic Rim clusters and asymmetric migration toward SEQ-03, giving the population inquiry a concrete regional topology. Exact Springview assignment and any SEQ-03/SEQ-West label crosswalk remain unresolved."
  true

------------------------------------------------------------------------
-- Legal atom bindings.
------------------------------------------------------------------------

record LocalPopulationAtomBinding : Set where
  constructor local-population-atom-binding
  field
    coordinate : Ibrahim.DashiKnowledgeCoordinate
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    sourceRole : LocalPopulationSourceRole
    geographicRelation : LocalPopulationRelation
    admissible : Bool
    sameObjectPaid : Bool
    consumerComplete : Bool
    contribution : String
    residual : String

open LocalPopulationAtomBinding public

busseyPopulationBinding : LocalPopulationAtomBinding
busseyPopulationBinding = local-population-atom-binding
  busseyEllisCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryResearchReport
  ipswichWide
  true false false
  "Moves the s 13 inquiry from generic SEQ Koala conservation toward an Ipswich-specific population/viability literature base."
  "Resolve the exact population unit used in the report and determine whether Springview/Woogaroo falls within the same biological population using current/local evidence."

whiteRockHabitatBinding : LocalPopulationAtomBinding
whiteRockHabitatBinding = local-population-atom-binding
  whiteRockCoreHabitatCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryLocalGovernmentPlan
  whiteRockSpringMountainAdjacent
  true false false
  "Pays independent government evidence that the adjacent White Rock-Spring Mountain landscape is managed as core Koala habitat and a regional corridor link exposed to Springfield-side development pressure."
  "Join Springview/Opossum-Woogaroo functional connectivity to this adjacent Core Habitat Area; adjacency alone does not pay essentiality."

seq03PopulationBinding : LocalPopulationAtomBinding
seq03PopulationBinding = local-population-atom-binding
  seq03GeneticCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryRegionalPopulationStudy
  regionalGeneticContext
  true false false
  "Supplies a concrete modern regional genetic topology through the Scenic Rim SEQ-03 cluster and migration analysis."
  "Do not infer an Ipswich or Springview assignment from the label alone. Resolve the SEQ-03/SEQ-West label relation, then obtain locality-appropriate samples/data or expert interpretation sufficient to identify the Springview/Woogaroo population."

------------------------------------------------------------------------
-- Updated acquisition frontier.
------------------------------------------------------------------------

record LocalPopulationFrontier : Set where
  constructor local-population-frontier
  field
    ipswichViabilityReportLocated : Bool
    adjacentCoreHabitatPlanLocated : Bool
    modernRegionalGeneticClusterLocated : Bool
    clusterLabelCrosswalkPaid : Bool
    exactSpringviewGeneticAssignmentPaid : Bool
    exactSpringviewViablePopulationIdentityPaid : Bool
    realisedConnectivityToWhiteRockPaid : Bool
    nextCut : String

currentLocalPopulationFrontier : LocalPopulationFrontier
currentLocalPopulationFrontier = local-population-frontier
  true true true
  false false false false
  "Highest-value next work: resolve the SEQ-03 versus SEQ-West cluster-label crosswalk; acquire the underlying Ipswich 2020/2023/2025 monitoring results already routed in ExistingLocalKoalaMonitoringSnowballExact; then ask a current ecologist whether Springview/Opossum-Woogaroo is functionally connected to White Rock-Spring Mountain and which viable/genetic population is implicated. Local genetic sampling is a fallback if existing data cannot resolve population identity."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

regionalAtlas : Source.AttributedSourceAtlas
regionalAtlas = Regional.regionalPopulationSourceAtlas

------------------------------------------------------------------------
-- Attribution / WrongType boundaries.
------------------------------------------------------------------------

data IpswichWideEqualsSpringviewPopulation : Set where
data SEQ03EqualsSEQWest : Set where
data AdjacentCoreHabitatEqualsSpringviewEssential : Set where
data CouncilPlanEqualsIndependentFieldReplication : Set where
data NoDOIEqualsNoSourceIdentity : Set where

ipswichWideDoesNotFixSpringviewPopulation : IpswichWideEqualsSpringviewPopulation → ⊥
ipswichWideDoesNotFixSpringviewPopulation ()

seq03DoesNotSilentlyBecomeSeqWest : SEQ03EqualsSEQWest → ⊥
seq03DoesNotSilentlyBecomeSeqWest ()

adjacentCoreHabitatDoesNotProveEssentiality : AdjacentCoreHabitatEqualsSpringviewEssential → ⊥
adjacentCoreHabitatDoesNotProveEssentiality ()

councilPlanDoesNotCreateFieldReplication : CouncilPlanEqualsIndependentFieldReplication → ⊥
councilPlanDoesNotCreateFieldReplication ()

noDoiDoesNotEraseSourceIdentity : NoDOIEqualsNoSourceIdentity → ⊥
noDoiDoesNotEraseSourceIdentity ()
