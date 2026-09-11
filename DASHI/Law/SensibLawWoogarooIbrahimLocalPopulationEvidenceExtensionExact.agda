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
-- Adds newly located primary/regional population sources that sharpen the
-- s 13 population-identity question.  This extends the existing Ibrahim/
-- Snowball graph; it does not create another traversal or legal ontology.
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

koalaDewey ecologyDewey conservationDewey : String
koalaDewey = "599.25"
ecologyDewey = "577"
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Newly located sources.
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
scenicRim2024 = Source.mkNoDOISource
  "Federation University; WildDNA; QWAD Environment"
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council"
  "2024"
  "https://www.scenicrim.qld.gov.au/downloads/file/6618/scenic-rim-2024-koala-study-report"
  (Source.namedSourceKind "primary regional genetic population study")
  "Primary regional genetic study using Koala genotypes and spatial clustering. It identifies multiple differentiated population clusters and reports that SEQ-03 has also been detected in large parts of Ipswich LGA. Used to constrain plausible regional population identity; it does not genetically assign Springview/Woogaroo without local samples."
  Source.publicAttribution

localPopulationAtlas : Source.AttributedSourceAtlas
localPopulationAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim local population evidence extension"
  "DASHI.Law.SensibLawWoogarooIbrahimLocalPopulationEvidenceExtensionExact"
  (busseyEllis2016 ∷ ipswichKoalaPlan ∷ scenicRim2024 ∷ [])
  "Local/regional population and corridor sources. Report authorship, institutional source, geographic scope and source role are explicit. No source is promoted into an exact Springview viable-population identity without a same-object spatial/genetic join."

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
  "SEQ-03 regional Koala genetic population cluster extending into Ipswich"
  ecologyDewey
  (Id.rawItemId southEastQueenslandQid)
  "Scenic Rim 2024 Koala population study; no DOI located"

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
  "Regional genetic evidence shows a differentiated cluster extends into large parts of Ipswich, giving the local population inquiry a concrete genetic hypothesis. Exact Springview assignment remains unresolved without local genetic data."
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
  "Supplies a concrete modern genetic population hypothesis: SEQ-03 is detected in large parts of Ipswich."
  "Obtain locality-appropriate samples/data or expert interpretation sufficient to determine whether Springview/Woogaroo animals are part of SEQ-03 or another population unit."

------------------------------------------------------------------------
-- Updated acquisition frontier.
------------------------------------------------------------------------

record LocalPopulationFrontier : Set where
  constructor local-population-frontier
  field
    ipswichViabilityReportLocated : Bool
    adjacentCoreHabitatPlanLocated : Bool
    modernRegionalGeneticClusterLocated : Bool
    exactSpringviewGeneticAssignmentPaid : Bool
    exactSpringviewViablePopulationIdentityPaid : Bool
    realisedConnectivityToWhiteRockPaid : Bool
    nextCut : String

currentLocalPopulationFrontier : LocalPopulationFrontier
currentLocalPopulationFrontier = local-population-frontier
  true true true
  false false false
  "Highest-value next work: read/extract the Bussey-Ellis population definitions and maps; acquire the underlying Ipswich 2020/2023/2025 monitoring results already routed in ExistingLocalKoalaMonitoringSnowballExact; then ask a current ecologist whether Springview/Opossum-Woogaroo is functionally connected to White Rock-Spring Mountain and which viable/genetic population is thereby implicated. Local genetic sampling is a fallback if existing data cannot resolve population identity."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

regionalAtlas : Source.AttributedSourceAtlas
regionalAtlas = Regional.regionalPopulationSourceAtlas

------------------------------------------------------------------------
-- Attribution / WrongType boundaries.
------------------------------------------------------------------------

data IpswichWideEqualsSpringviewPopulation : Set where
data SEQ03InIpswichEqualsSpringviewSEQ03 : Set where
data AdjacentCoreHabitatEqualsSpringviewEssential : Set where
data CouncilPlanEqualsIndependentFieldReplication : Set where
data NoDOIEqualsNoSourceIdentity : Set where

ipswichWideDoesNotFixSpringviewPopulation : IpswichWideEqualsSpringviewPopulation → ⊥
ipswichWideDoesNotFixSpringviewPopulation ()

seq03IpswichDoesNotAssignSpringview : SEQ03InIpswichEqualsSpringviewSEQ03 → ⊥
seq03IpswichDoesNotAssignSpringview ()

adjacentCoreHabitatDoesNotProveEssentiality : AdjacentCoreHabitatEqualsSpringviewEssential → ⊥
adjacentCoreHabitatDoesNotProveEssentiality ()

councilPlanDoesNotCreateFieldReplication : CouncilPlanEqualsIndependentFieldReplication → ⊥
councilPlanDoesNotCreateFieldReplication ()

noDoiDoesNotEraseSourceIdentity : NoDOIEqualsNoSourceIdentity → ⊥
noDoiDoesNotEraseSourceIdentity ()
