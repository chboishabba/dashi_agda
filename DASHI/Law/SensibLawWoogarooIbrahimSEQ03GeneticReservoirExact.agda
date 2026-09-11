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
-- IBRAHIM / SNOWBALL: SEQ-03 GENETIC-RESERVOIR NARROWING
--
-- Highest-alpha population follow.  This does not declare that Springview /
-- Woogaroo belongs to SEQ-03.  It narrows the acquisition question from an
-- undifferentiated SEQ population to a contemporary genetic-cluster candidate
-- whose conservation geography explicitly reaches the Ipswich/Logan context.
------------------------------------------------------------------------

data ClaimRelativeRole : Set where
  primaryGovernmentHostedTechnicalReport : ClaimRelativeRole
  bibliographicMirrorSameObject : ClaimRelativeRole
  primaryLocalGovernmentContext : ClaimRelativeRole

data PopulationNexusStatus : Set where
  regionalClusterPaid : PopulationNexusStatus
  crossLgaConservationNexusPaid : PopulationNexusStatus
  springviewMembershipOpen : PopulationNexusStatus
  essentialityOpen : PopulationNexusStatus

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

southEastQueenslandQid : Id.ItemId
southEastQueenslandQid = Id.itemId "Q1894392"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

koalaDewey : String
koalaDewey = "599.25"

populationGeneticsDewey : String
populationGeneticsDewey = "576.5"

conservationDewey : String
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Attributed source identity.
------------------------------------------------------------------------

scenicRim2024PopulationStudy : Source.AttributedSource
scenicRim2024PopulationStudy = Source.mkDOISource
  "Olivia Woosnam; Fiona E. Hogan"
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council / Federation University / WildDNA / OWAD Environment technical report"
  "2025"
  "10.13140/RG.2.2.24954.20163"
  "https://www.scenicrim.qld.gov.au/files/assets/public/v/1/our-environment/biodiversity/koalas/documents/scenicrim_2024koalastudyreport_final.pdf"
  (Source.namedSourceKind "government-hosted genetic population technical report")
  "Primary technical report for a non-invasive Scenic Rim koala genetic study. It identifies five clusters within the Scenic Rim study area, asymmetric migration toward SEQ-03, and characterises SEQ-03 as a high-conservation-significance genetic reservoir in a fragmented landscape facing development pressure including Ipswich and Logan. Used to narrow the Woogaroo population-identification question; it does not establish that Springview animals belong to SEQ-03."
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

seq03SourceAtlas : Source.AttributedSourceAtlas
seq03SourceAtlas = Source.mkSourceAtlas
  "Woogaroo SEQ-03 genetic-reservoir Snowball"
  "DASHI.Law.SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact"
  (scenicRim2024PopulationStudy ∷ ipswichCurrentKoalaContext ∷ [])
  "Government-hosted contemporary genetic-population report plus current Ipswich institutional context. DOI, QID, Dewey and URL coordinates preserve provenance/navigation only. Neither source establishes Springview membership in SEQ-03 or statutory s 13 essentiality."

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

------------------------------------------------------------------------
-- Ibrahim coordinate and traversal.
------------------------------------------------------------------------

seq03Coordinate : Ibrahim.DashiKnowledgeCoordinate
seq03Coordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact.agda"
  "SEQ-03 contemporary koala genetic-reservoir / migration cluster candidate"
  (populationGeneticsDewey ++ " / " ++ koalaDewey)
  (Id.rawItemId southEastQueenslandQid)
  "doi:10.13140/RG.2.2.24954.20163; primary: Scenic Rim Regional Council hosted report"

ipswichGeneticContextCoordinate : Ibrahim.DashiKnowledgeCoordinate
ipswichGeneticContextCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact.agda"
  "Ipswich regionally significant / genetically distinctive koala population context"
  (conservationDewey ++ " / " ++ koalaDewey)
  (Id.rawItemId cityOfIpswichQid)
  "primary: Ipswich City Council Koala Conservation"

seq03ToS13 : Ibrahim.DashiFirstLinkEdge
seq03ToS13 = Ibrahim.dashi-first-link-edge
  seq03Coordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Contemporary genetics materially narrows the candidate population topology: SEQ-03 is a genetically defined conservation-significant reservoir receiving asymmetric migration and the report expressly identifies Ipswich/Logan development pressure in its landscape context. The exact Springview/Woogaroo animals still require a same-object genetic/demographic join before SEQ-03 can be used as their population identity."
  true

ipswichContextToS13 : Ibrahim.DashiFirstLinkEdge
ipswichContextToS13 = Ibrahim.dashi-first-link-edge
  ipswichGeneticContextCoordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Ipswich Council independently treats the Ipswich population as regionally significant and genetically distinctive. This supports the importance of acquiring the existing local monitoring/genetic evidence, not a conclusion that Springview habitat is essential."
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

seq03S13Binding : PopulationAtomBinding
seq03S13Binding = population-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryGovernmentHostedTechnicalReport
  "Contemporary SEQ genetic clustering, asymmetric migration and a conservation-significant SEQ-03 reservoir are source-paid as regional population structure; Ipswich is independently source-paid as regionally significant/genetically distinctive context."
  "Determine whether Springview/Woogaroo koalas belong to SEQ-03 or another independently characterised cluster/subpopulation, using existing Ipswich 2020/2023/2025 monitoring/genetic/rescue records or new targeted genetics only if existing records cannot resolve the question."
  "SEQ-03 conservation significance and Ipswich genetic uniqueness do not establish Springview population membership, viability, or the s 13 essentiality of the project habitat."

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record SEQ03Frontier : Set where
  constructor seq03-frontier
  field
    contemporaryClusterTopologyPaid : Bool
    seq03ReservoirImportancePaid : Bool
    ipswichGeneticSignificanceContextPaid : Bool
    springviewSeq03MembershipPaid : Bool
    localPopulationBoundaryPaid : Bool
    withoutSiteCounterfactualPaid : Bool
    nextAction : String

currentSEQ03Frontier : SEQ03Frontier
currentSEQ03Frontier = seq03-frontier
  true true true false false false
  "Acquire existing Ipswich/Biolink 2020, 2023 and 2025 site-level monitoring outputs and any available non-invasive genetic/population assignments; request locality-appropriate IKPS/Moggill records. Test whether those records can place Springview/Woogaroo within SEQ-03 or another defensible subpopulation before commissioning new genetics. If identity is resolved, calculate the without-Springview connectivity/persistence counterfactual for s 13 and reuse the effect pathway for s 102."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

localNexusAtlas : Source.AttributedSourceAtlas
localNexusAtlas = Local.localPopulationNexusAtlas

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SEQ03MeansSpringviewPopulation : Set where
data IpswichGeneticUniquenessMeansSEQ03 : Set where
data ResearchGateMirrorMeansIndependentSource : Set where
data RegionalReservoirMeansS13Essentiality : Set where
data ClusterMigrationMeansWoogarooFunctionalConnectivity : Set where
data DoiMeansSameObjectJoin : Set where
data QidMeansPopulationBoundary : Set where
data DeweyMeansEvidence : Set where

seq03DoesNotIdentifySpringview : SEQ03MeansSpringviewPopulation → ⊥
seq03DoesNotIdentifySpringview ()

ipswichContextDoesNotAssignSEQ03 : IpswichGeneticUniquenessMeansSEQ03 → ⊥
ipswichContextDoesNotAssignSEQ03 ()

mirrorDoesNotCreateIndependence : ResearchGateMirrorMeansIndependentSource → ⊥
mirrorDoesNotCreateIndependence ()

reservoirDoesNotCreateEssentiality : RegionalReservoirMeansS13Essentiality → ⊥
reservoirDoesNotCreateEssentiality ()

migrationDoesNotCreateWoogarooConnectivity : ClusterMigrationMeansWoogarooFunctionalConnectivity → ⊥
migrationDoesNotCreateWoogarooConnectivity ()

doiDoesNotCreateSameObjectJoin : DoiMeansSameObjectJoin → ⊥
doiDoesNotCreateSameObjectJoin ()

qidDoesNotCreatePopulationBoundary : QidMeansPopulationBoundary → ⊥
qidDoesNotCreatePopulationBoundary ()

deweyDoesNotCreateEvidence : DeweyMeansEvidence → ⊥
deweyDoesNotCreateEvidence ()
