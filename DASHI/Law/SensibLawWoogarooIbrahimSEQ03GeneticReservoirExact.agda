module DASHI.Law.SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact as Local
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL: SEQ POPULATION-GENETIC NARROWING
--
-- Highest-alpha population follow.  Two source lineages currently use two
-- cluster labels: SEQ-03 and SEQ West.  They are retained as distinct labels
-- unless a source-paid crosswalk proves identity.  Neither label is assigned
-- to Springview / Woogaroo without a same-object population join.
------------------------------------------------------------------------

data ClaimRelativeRole : Set where
  primaryGovernmentHostedTechnicalReport : ClaimRelativeRole
  primaryAuthoredTechnicalReport : ClaimRelativeRole
  approvedAdjacentConsultantReport : ClaimRelativeRole
  bibliographicMirrorSameObject : ClaimRelativeRole
  primaryLocalGovernmentContext : ClaimRelativeRole

data PopulationNexusStatus : Set where
  regionalClusterPaid : PopulationNexusStatus
  crossLgaConservationNexusPaid : PopulationNexusStatus
  clusterLabelCrosswalkOpen : PopulationNexusStatus
  springviewMembershipOpen : PopulationNexusStatus
  essentialityOpen : PopulationNexusStatus

data ClusterLabel : Set where
  seq03
  seqWest : ClusterLabel

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

southEastQueenslandQid : Id.ItemId
southEastQueenslandQid = Id.itemId "Q1894392"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

populationGeneticsQid : Id.ItemId
populationGeneticsQid = Id.itemId "Q31151"

geneFlowQid : Id.ItemId
geneFlowQid = Id.itemId "Q143089"

koalaDewey : String
koalaDewey = "599.25"

populationGeneticsDewey : String
populationGeneticsDewey = "576.58"

conservationDewey : String
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Attributed source identity.
------------------------------------------------------------------------

scenicRim2024PopulationStudy : Source.AttributedSource
scenicRim2024PopulationStudy = Source.mkDOISource
  "Olivia Woosnam; Fiona E. Hogan"
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council / OWAD Environment / WildDNA / Federation University technical report"
  "2025"
  "10.13140/RG.2.2.24954.20163"
  "https://www.scenicrim.qld.gov.au/files/assets/public/v/1/our-environment/biodiversity/koalas/documents/scenicrim_2024koalastudyreport_final.pdf"
  (Source.namedSourceKind "government-hosted genetic population technical report")
  "Primary government-hosted technical report for a non-invasive Scenic Rim koala genetic study. It identifies five clusters within the Scenic Rim study area and asymmetric migration toward the cluster labelled SEQ-03. Used to constrain regional population topology; it does not establish that SEQ-03 and the separately named SEQ West cluster are identical, nor that Springview animals belong to either."
  Source.publicAttribution

brisbane2018PopulationStudy : Source.AttributedSource
brisbane2018PopulationStudy = Source.mkDOISource
  "Olivia Woosnam; Alex Dudkowski; Fiona E. Hogan; Faye Wedrowicz"
  "2018 Brisbane City Council Koala Population Study"
  "OWAD Environment / WildDNA / Federation University; technical report for Brisbane City Council"
  "2018"
  "10.13140/RG.2.2.35284.12164"
  "https://doi.org/10.13140/RG.2.2.35284.12164"
  (Source.namedSourceKind "primary authored genetic population technical report")
  "Primary authored Brisbane population/genetics report. It supplies the published landscape-scale cluster map later reused by the Tarnbrae report. Its own map warns that cluster boundaries are landscape-scale, incomplete and not suitable for fine-scale assignment."
  Source.publicAttribution

tarnbrae2023KoalaSurvey : Source.AttributedSource
tarnbrae2023KoalaSurvey = Source.mkNoDOISource
  "Olivia Woosnam"
  "Koala survey report — Tarnbrae"
  "OWAD Environment report prepared for Litoria Consulting; incorporated in approved DEV2023/1413 Significant Biodiversity Assessment material"
  "2023"
  "https://edqdad.dsdip.qld.gov.au/developmentAssessments/attachments/view/25031/"
  (Source.namedSourceKind "approved adjacent-project consultant genetic survey")
  "Primary consultant survey embedded in a government-hosted approved development-assessment carrier. It states that SEQ West had been confirmed/detected in Brisbane, Lockyer Valley, Ipswich and Scenic Rim LGAs, but explicitly says site-level cluster assignment is speculative without reliable local DNA profiles. Used as an acquisition-method and regional-cluster lead, not as Springview population identity."
  Source.publicAttribution

ipswichCurrentKoalaContext : Source.AttributedSource
ipswichCurrentKoalaContext = Source.mkNoDOISource
  "Ipswich City Council"
  "Koala Conservation"
  "Ipswich City Council current wildlife/conservation page"
  "2026"
  "https://www.ipswich.qld.gov.au/About-Council/Initiatives/Environment/Wildlife/Koala-Conservation"
  Source.governmentSource
  "Primary local-government context source stating that Ipswich's koala population is regionally significant due to its size and genetic uniqueness, and that habitat loss/fragmentation from urban and industrial development is a key threatening process locally. Used as local institutional context, not as a genetic sample or site-population boundary."
  Source.publicAttribution

seqPopulationSourceAtlas : Source.AttributedSourceAtlas
seqPopulationSourceAtlas = Source.mkSourceAtlas
  "Woogaroo SEQ population-genetic Snowball"
  "DASHI.Law.SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact"
  (scenicRim2024PopulationStudy ∷ brisbane2018PopulationStudy ∷ tarnbrae2023KoalaSurvey ∷ ipswichCurrentKoalaContext ∷ [])
  "Government-hosted contemporary genetic-population reports, an authored Brisbane genetic report, an adjacent approved survey and current Ipswich institutional context. DOI, QID, Dewey and URL coordinates preserve provenance/navigation only. SEQ-03 and SEQ West remain distinct labels until a source-paid crosswalk is located; no source establishes Springview membership or statutory s 13 essentiality."

------------------------------------------------------------------------
-- Same-object DOI/mirror discipline.
------------------------------------------------------------------------

record SameObjectAliasReceipt : Set where
  constructor same-object-alias-receipt
  field
    canonicalObject : String
    officialLink : String
    bibliographicMirror : String
    mirrorDoi : String
    countAsIndependentEvidence : Bool

scenicRimReportAlias : SameObjectAliasReceipt
scenicRimReportAlias = same-object-alias-receipt
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council hosted PDF"
  "ResearchGate bibliographic/full-text record"
  "10.13140/RG.2.2.24954.20163"
  false

brisbaneReportAlias : SameObjectAliasReceipt
brisbaneReportAlias = same-object-alias-receipt
  "2018 Brisbane City Council Koala Population Study"
  "authored technical report"
  "ResearchGate author-uploaded full-text/bibliographic record"
  "10.13140/RG.2.2.35284.12164"
  false

------------------------------------------------------------------------
-- Cluster-label identity discipline.
------------------------------------------------------------------------

record ClusterLabelIdentityState : Set where
  constructor cluster-label-identity-state
  field
    leftLabel : ClusterLabel
    rightLabel : ClusterLabel
    sameClusterPaid : Bool
    evidence : String
    nextSearch : String

seq03SeqWestIdentity : ClusterLabelIdentityState
seq03SeqWestIdentity = cluster-label-identity-state
  seq03 seqWest false
  "Scenic Rim 2024 uses the label SEQ-03; Tarnbrae 2023 uses SEQ West and cites the 2018 Brisbane population map. The inspected sources do not themselves prove these labels denote the same genetic cluster."
  "Locate the underlying OWAD/WildDNA regional cluster crosswalk or publication/dataset that maps SEQ-03 to SEQ West/Cluster 3 before merging the labels."

------------------------------------------------------------------------
-- Ibrahim coordinates and traversal.
------------------------------------------------------------------------

seq03Coordinate : Ibrahim.DashiKnowledgeCoordinate
seq03Coordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact.agda"
  "SEQ-03 Scenic Rim koala genetic cluster / asymmetric migration target"
  populationGeneticsDewey
  (Id.rawItemId populationGeneticsQid)
  "doi:10.13140/RG.2.2.24954.20163; primary: Scenic Rim Regional Council hosted report"

seqWestCoordinate : Ibrahim.DashiKnowledgeCoordinate
seqWestCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact.agda"
  "SEQ West koala genetic cluster / regional population hypothesis"
  populationGeneticsDewey
  (Id.rawItemId geneFlowQid)
  "primary: OWAD Tarnbrae survey in approved DEV2023/1413 carrier; published-map lineage doi:10.13140/RG.2.2.35284.12164"

ipswichGeneticContextCoordinate : Ibrahim.DashiKnowledgeCoordinate
ipswichGeneticContextCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact.agda"
  "Ipswich regionally significant / genetically distinctive koala population context"
  conservationDewey
  (Id.rawItemId cityOfIpswichQid)
  "primary: Ipswich City Council Koala Conservation"

seq03ToS13 : Ibrahim.DashiFirstLinkEdge
seq03ToS13 = Ibrahim.dashi-first-link-edge
  seq03Coordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Contemporary Scenic Rim genetics narrows the population topology and demonstrates asymmetric migration among differentiated clusters. The exact Springview/Woogaroo population remains unresolved."
  true

seqWestToS13 : Ibrahim.DashiFirstLinkEdge
seqWestToS13 = Ibrahim.dashi-first-link-edge
  seqWestCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The Tarnbrae report makes the acquisition requirement unusually explicit: regional geography may suggest a cluster, but reliable local DNA is required to verify site population assignment. That same identity discipline applies to Springview."
  true

ipswichContextToS13 : Ibrahim.DashiFirstLinkEdge
ipswichContextToS13 = Ibrahim.dashi-first-link-edge
  ipswichGeneticContextCoordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Ipswich Council independently treats the Ipswich population as regionally significant and genetically distinctive. This supports acquisition of existing local monitoring/genetic evidence, not a conclusion that Springview habitat is essential."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record PopulationAtomBinding : Set where
  constructor population-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    sourceRole : ClaimRelativeRole
    currentPayment : String
    firstUnpaidJoin : String
    promotionBoundary : String

open PopulationAtomBinding public

seqPopulationS13Binding : PopulationAtomBinding
seqPopulationS13Binding = population-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryGovernmentHostedTechnicalReport
  "Regional genetic differentiation and population structure are source-paid. SEQ-03 is source-paid as a Scenic Rim cluster receiving asymmetric migration; SEQ West is separately source-paid as a cluster reported as detected across Brisbane, Lockyer Valley, Ipswich and Scenic Rim by the Tarnbrae source lineage."
  "First resolve whether SEQ-03 and SEQ West are the same population label; then determine which cluster/subpopulation, if any, Springview/Woogaroo koalas belong to using existing Ipswich 2020/2023/2025 monitoring/genetic/rescue records or targeted local genetics only if existing records cannot resolve the question."
  "Regional cluster existence, Ipswich-wide occurrence of a cluster label and genetic significance do not establish Springview population membership, population viability, realised connectivity or s 13 essentiality."

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record SEQPopulationFrontier : Set where
  constructor seq-population-frontier
  field
    scenicRimClusterTopologyPaid : Bool
    seqWestRegionalDistributionClaimPaid : Bool
    brisbaneLandscapeClusterMapPaid : Bool
    seq03EqualsSeqWestPaid : Bool
    ipswichGeneticSignificanceContextPaid : Bool
    springviewClusterMembershipPaid : Bool
    localPopulationBoundaryPaid : Bool
    withoutSiteCounterfactualPaid : Bool
    nextAction : String

currentSEQPopulationFrontier : SEQPopulationFrontier
currentSEQPopulationFrontier = seq-population-frontier
  true true true false true false false false
  "Highest-alpha order: (1) locate an authoritative cluster-label crosswalk for SEQ-03 versus SEQ West/Cluster 3; (2) acquire existing Ipswich/Biolink 2020, 2023 and 2025 site-level monitoring outputs and any local genotype/population assignments; (3) request locality-appropriate IKPS/Moggill records; (4) only if existing data cannot identify the relevant population, commission targeted non-invasive genetics. Once population identity is paid, calculate the without-Springview connectivity/persistence counterfactual for s 13 and reuse the causal pathway for s 102."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

localNexusAtlas : Source.AttributedSourceAtlas
localNexusAtlas = Local.localPopulationNexusAtlas

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SEQ03EqualsSEQWest : Set where
data SEQWestInIpswichEqualsSpringviewSEQWest : Set where
data IpswichGeneticUniquenessMeansClusterAssignment : Set where
data ResearchGateMirrorMeansIndependentSource : Set where
data RegionalClusterMeansS13Essentiality : Set where
data ClusterMigrationMeansWoogarooFunctionalConnectivity : Set where
data DoiMeansSameObjectJoin : Set where
data QidMeansPopulationBoundary : Set where
data DeweyMeansEvidence : Set where

seq03DoesNotSilentlyBecomeSeqWest : SEQ03EqualsSEQWest → ⊥
seq03DoesNotSilentlyBecomeSeqWest ()

seqWestIpswichDoesNotAssignSpringview : SEQWestInIpswichEqualsSpringviewSEQWest → ⊥
seqWestIpswichDoesNotAssignSpringview ()

ipswichContextDoesNotAssignCluster : IpswichGeneticUniquenessMeansClusterAssignment → ⊥
ipswichContextDoesNotAssignCluster ()

mirrorDoesNotCreateIndependence : ResearchGateMirrorMeansIndependentSource → ⊥
mirrorDoesNotCreateIndependence ()

regionalClusterDoesNotCreateEssentiality : RegionalClusterMeansS13Essentiality → ⊥
regionalClusterDoesNotCreateEssentiality ()

migrationDoesNotCreateWoogarooConnectivity : ClusterMigrationMeansWoogarooFunctionalConnectivity → ⊥
migrationDoesNotCreateWoogarooFunctionalConnectivity ()

doiDoesNotCreateSameObjectJoin : DoiMeansSameObjectJoin → ⊥
doiDoesNotCreateSameObjectJoin ()

qidDoesNotCreatePopulationBoundary : QidMeansPopulationBoundary → ⊥
qidDoesNotCreatePopulationBoundary ()

deweyDoesNotCreateEvidence : DeweyMeansEvidence → ⊥
deweyDoesNotCreateEvidence ()
