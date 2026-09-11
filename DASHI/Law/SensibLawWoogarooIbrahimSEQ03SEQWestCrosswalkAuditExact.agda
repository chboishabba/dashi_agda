module DASHI.Law.SensibLawWoogarooIbrahimSEQ03SEQWestCrosswalkAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooIbrahimSEQ03GeneticReservoirExact as Reservoir
import DASHI.Law.SensibLawWoogarooIbrahimPopulationValidationSotaExact as Validation
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- IBRAHIM FOLLOW: SEQ-03 / SEQ-WEST CLUSTER CROSSWALK AUDIT
--
-- The current Snowball has two primary lineages using different names for
-- regional koala genetic structure.  This owner tests identity and fails
-- closed.  Similar geography, conservation significance, cluster number or
-- colour are acquisition clues only until one source explicitly bridges the
-- labels or the underlying genotype/cluster assignments pay the crosswalk.
------------------------------------------------------------------------

data CrosswalkStatus : Set where
  exactIdentityPaid
  compatibleButUnpaid
  evidenceAgainstIdentity
  unresolved : CrosswalkStatus

data CrosswalkEvidenceRole : Set where
  primaryPopulationReport
  primaryApprovedSurvey
  primaryGeneticDataset
  secondarySignpost : CrosswalkEvidenceRole

populationGeneticsQid : Id.ItemId
populationGeneticsQid = Canonical.populationGeneticsQid

geneFlowQid : Id.ItemId
geneFlowQid = Canonical.geneFlowQid

populationGeneticsDewey : String
populationGeneticsDewey = Canonical.populationGeneticsDewey

------------------------------------------------------------------------
-- Attributed source identities.
------------------------------------------------------------------------

brisbane2018 : Source.AttributedSource
brisbane2018 = Source.mkDOISource
  "Olivia Woosnam; Alex Dudkowski; Fiona E. Hogan; Faye Wedrowicz"
  "2018 Brisbane City Council Koala Population Study"
  "OWAD Environment / WildDNA / Federation University; technical report for Brisbane City Council"
  "2018"
  "10.13140/RG.2.2.35284.12164"
  "https://doi.org/10.13140/RG.2.2.35284.12164"
  (Source.namedSourceKind "primary authored genetic population technical report")
  "Primary source for the three-cluster Brisbane-and-surrounds population map. Later approved-survey material calls the purple Cluster 3 on this map 'SEQ West'. The 2018 report itself does not use the later Scenic Rim label SEQ-03 in the material inspected here."
  Source.publicAttribution

tarnbrae2023 : Source.AttributedSource
tarnbrae2023 = Source.mkNoDOISource
  "Olivia Woosnam"
  "Koala survey report — Tarnbrae"
  "OWAD Environment report in approved DEV2023/1413 Significant Biodiversity Assessment material"
  "2023"
  "https://edqdad.dsdip.qld.gov.au/developmentAssessments/attachments/view/25031/"
  (Source.namedSourceKind "primary approved adjacent-project genetic survey")
  "Primary approved-survey carrier explicitly stating that the SEQ West population cluster is Cluster 3 shown in purple on the 2018 Brisbane population map and has been detected in Brisbane, Lockyer Valley, Ipswich and Scenic Rim LGAs. It also states site-level population assignment is speculative without reliable local DNA profiles."
  Source.publicAttribution

scenicRim2024 : Source.AttributedSource
scenicRim2024 = Source.mkDOISource
  "Olivia Woosnam; Fiona E. Hogan"
  "Scenic Rim 2024 Koala population study"
  "Scenic Rim Regional Council / OWAD Environment / WildDNA / Federation University technical report"
  "2025"
  "10.13140/RG.2.2.24954.20163"
  "https://www.scenicrim.qld.gov.au/files/assets/public/v/1/our-environment/biodiversity/koalas/documents/scenicrim_2024koalastudyreport_final.pdf"
  (Source.namedSourceKind "primary government-hosted genetic population technical report")
  "Primary Scenic Rim population-genetics carrier. It names clusters SEQ-03 through SEQ-07, identifies SEQ-03 as a high-conservation-significance genetic reservoir receiving most detected migration from several other clusters, and says its full extent may extend north/west beyond currently sampled areas. The inspected text does not explicitly equate SEQ-03 with SEQ West/Cluster 3."
  Source.publicAttribution

crosswalkAtlas : Source.AttributedSourceAtlas
crosswalkAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim SEQ-03 / SEQ-West crosswalk audit"
  "DASHI.Law.SensibLawWoogarooIbrahimSEQ03SEQWestCrosswalkAuditExact"
  (brisbane2018 ∷ tarnbrae2023 ∷ scenicRim2024 ∷ [])
  "Three primary population/genetic-report carriers. Same authorship or overlapping geography does not create label identity. The crosswalk remains unpaid until explicit source text, shared genotype assignments or an authoritative cluster-key/dataset connects the two label systems."

------------------------------------------------------------------------
-- Ibrahim coordinates.
------------------------------------------------------------------------

seqWestCluster3Coordinate : Ibrahim.DashiKnowledgeCoordinate
seqWestCluster3Coordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03SEQWestCrosswalkAuditExact.agda"
  "SEQ West / Cluster 3 (purple) regional koala genetic cluster"
  populationGeneticsDewey
  (Id.rawItemId geneFlowQid)
  "Tarnbrae 2023 -> Brisbane 2018 map; DOI 10.13140/RG.2.2.35284.12164"

seq03Coordinate : Ibrahim.DashiKnowledgeCoordinate
seq03Coordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimSEQ03SEQWestCrosswalkAuditExact.agda"
  "SEQ-03 Scenic Rim genetic reservoir / migration sink"
  populationGeneticsDewey
  (Id.rawItemId populationGeneticsQid)
  "Scenic Rim 2024 study; DOI 10.13140/RG.2.2.24954.20163"

------------------------------------------------------------------------
-- Evidence audit.
------------------------------------------------------------------------

record CrosswalkEvidence : Set where
  constructor crosswalk-evidence
  field
    role : CrosswalkEvidenceRole
    sourceLabel : String
    supportsCompatibility : Bool
    paysIdentity : Bool
    evidence : String
    boundary : String

open CrosswalkEvidence public

tarnbraeClusterKey : CrosswalkEvidence
tarnbraeClusterKey = crosswalk-evidence
  primaryApprovedSurvey
  "Tarnbrae 2023"
  true false
  "Explicitly crosswalks SEQ West to Cluster 3/purple on the 2018 Brisbane map and says that cluster has been detected across Brisbane, Lockyer Valley, Ipswich and Scenic Rim."
  "This pays SEQ West = 2018 Cluster 3, not SEQ West = Scenic Rim SEQ-03."

scenicRimSeq03Topology : CrosswalkEvidence
scenicRimSeq03Topology = crosswalk-evidence
  primaryPopulationReport
  "Scenic Rim 2024"
  true false
  "SEQ-03 is a high-significance genetic reservoir, receives most detected migration from SEQ-04/05/06/07, and is relevant to coordinated conservation across Scenic Rim, Ipswich, Brisbane and Logan."
  "Geographic overlap and the numeric suffix '03' are insufficient to identify it with the independently named Cluster 3/SEQ West."

sharedProducerLineage : CrosswalkEvidence
sharedProducerLineage = crosswalk-evidence
  secondarySignpost
  "OWAD/WildDNA/Federation methodological lineage"
  true false
  "The Brisbane, Tarnbrae and Scenic Rim carriers share overlapping producer/authorship lineage, making an intentional renaming/crosswalk plausible and worth retrieving from underlying project data or reports."
  "Shared producers do not make differently labelled clusters identical."

record CrosswalkState : Set where
  constructor crosswalk-state
  field
    seqWestEqualsBrisbaneCluster3Paid : Bool
    seq03RegionalTopologyPaid : Bool
    seq03EqualsSeqWestPaid : Bool
    currentStatus : CrosswalkStatus
    firstUnpaidCarrier : String
    fallback : String

currentCrosswalkState : CrosswalkState
currentCrosswalkState = crosswalk-state
  true true false compatibleButUnpaid
  "Acquire an explicit OWAD/WildDNA cluster key, underlying genotype assignment table/dataset, or source passage mapping the Brisbane 2018 Cluster 3/SEQ West label to the Scenic Rim SEQ-03 label."
  "If no published crosswalk exists, preserve both labels as distinct and move to locality-specific Ipswich/Springview monitoring or DNA rather than infer identity from numbering, colour or geography."

------------------------------------------------------------------------
-- Legal-atom consequence.
------------------------------------------------------------------------

record CrosswalkAtomBinding : Set where
  constructor crosswalk-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    regionalStructureAdmissible : Bool
    crosswalkRequiredForLocalPopulationIdentity : Bool
    crosswalkAloneWouldCompleteAtom : Bool
    currentContribution : String
    residual : String

open CrosswalkAtomBinding public

s13CrosswalkBinding : CrosswalkAtomBinding
s13CrosswalkBinding = crosswalk-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false false
  "Regional genetic structure is admissible context for defining population questions. Resolving the label crosswalk would improve regional topology/provenance but is not itself required to identify the local Springview viable population."
  "The decisive s 13 evidence remains locality-specific: existing Ipswich monitoring/genetic/rescue data, realised connectivity, and the without-Springview counterfactual."

seq03ToS13 : Ibrahim.DashiFirstLinkEdge
seq03ToS13 = Ibrahim.dashi-first-link-edge
  seq03Coordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "SEQ-03 topology sharpens the regional population hypothesis but does not pay Springview membership or essentiality."
  true

seqWestToS13 : Ibrahim.DashiFirstLinkEdge
seqWestToS13 = Ibrahim.dashi-first-link-edge
  seqWestCluster3Coordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "SEQ West/Cluster 3 gives a second regional population label with an Ipswich distribution claim, but local membership remains a same-object evidence question."
  true

------------------------------------------------------------------------
-- WrongType / attribution boundaries.
------------------------------------------------------------------------

data SameNumberMeansSameCluster : Set where
data SameColourMeansSameCluster : Set where
data SameAuthorsMeanSameCluster : Set where
data OverlappingLGAsMeanSameCluster : Set where
data RegionalClusterIdentityEqualsSpringviewMembership : Set where
data CrosswalkPaidEqualsS13Essentiality : Set where

sameNumberDoesNotProveClusterIdentity : SameNumberMeansSameCluster → ⊥
sameNumberDoesNotProveClusterIdentity ()

sameColourDoesNotProveClusterIdentity : SameColourMeansSameCluster → ⊥
sameColourDoesNotProveClusterIdentity ()

sameAuthorsDoNotProveClusterIdentity : SameAuthorsMeanSameCluster → ⊥
sameAuthorsDoNotProveClusterIdentity ()

overlappingLGAsDoNotProveClusterIdentity : OverlappingLGAsMeanSameCluster → ⊥
overlappingLGAsDoNotProveClusterIdentity ()

regionalIdentityDoesNotCreateSpringviewMembership : RegionalClusterIdentityEqualsSpringviewMembership → ⊥
regionalIdentityDoesNotCreateSpringviewMembership ()

crosswalkDoesNotCreateEssentiality : CrosswalkPaidEqualsS13Essentiality → ⊥
crosswalkDoesNotCreateEssentiality ()

------------------------------------------------------------------------
-- Reuse existing reservoirs / validation rather than re-owning them.
------------------------------------------------------------------------

reservoirState : Reservoir.SEQPopulationFrontier
reservoirState = Reservoir.currentSEQPopulationFrontier

validationLadder : Validation.PopulationValidationLadder
validationLadder = Validation.currentPopulationValidationLadder
