module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationProvenanceGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.TypedProvenanceDependencyGraphExact as Provenance
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Structural
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as Uncertainty

------------------------------------------------------------------------
-- ADK CALIBRATION PROVENANCE DEPENDENCY GRAPH
--
-- This is an instance of the repository-wide typed provenance graph, not a new
-- provenance calculus.  It separates source family from dependency role and
-- marks only the dependencies actually required for a downstream payment.
------------------------------------------------------------------------

articleNode : Provenance.DependencyNode
articleNode = Provenance.dependencyNode
  "Li-Liu-Ji 2015 AdK article identity"
  Provenance.scholarlyLiterature
  "source-bounded article DOI/PMID/PMCID and reported AdK landscape premises"
  false

openStructureNode : Provenance.DependencyNode
openStructureNode = Provenance.dependencyNode
  "4AKE open structural manifestation"
  Provenance.empiricalDataset
  "PDB deposition identity, PDB DOI and open structural reference"
  false

closedStructureNode : Provenance.DependencyNode
closedStructureNode = Provenance.dependencyNode
  "1AKE closed structural manifestation"
  Provenance.empiricalDataset
  "PDB deposition identity, PDB DOI and closed structural reference"
  false

uniprotNode : Provenance.DependencyNode
uniprotNode = Provenance.dependencyNode
  "UniProt P69441 protein identity"
  Provenance.empiricalDataset
  "shared E. coli adenylate-kinase protein navigation identity"
  false

adkQidNode : Provenance.DependencyNode
adkQidNode = Provenance.dependencyNode
  "Wikidata Q356240 adenylate-kinase identity"
  Provenance.wikidataData
  "supplemental external entity identity; does not create PDB-object identity"
  false

sparseKernelNode : Provenance.DependencyNode
sparseKernelNode = Provenance.dependencyNode
  "DASHI sparse attributed transition kernel"
  Provenance.dashiFormal
  "typed topology/state/rate/path-flux carrier with explicit missingness"
  false

manifestationGuardNode : Provenance.DependencyNode
manifestationGuardNode = Provenance.dependencyNode
  "same-object supporting-material manifestation guard"
  Provenance.dashiFormal
  "blocks foreign PII and unreceipted visual readout from paying AdK calibration"
  false

runtimeAcquisitionNode : Provenance.DependencyNode
runtimeAcquisitionNode = Provenance.dependencyNode
  "locator-specific numeric acquisition receipt"
  Provenance.runtimeAcquisition
  "future same-object machine-readable or separately receipted numeric value"
  false

uncertaintyNode : Provenance.DependencyNode
uncertaintyNode = Provenance.dependencyNode
  "metadynamics free-energy uncertainty envelope"
  Provenance.dashiFormal
  "retains source-reported approximately 0.5 kcal/mol uncertainty for paid BE-META free energies"
  false

paidNumericCellNode : Provenance.DependencyNode
paidNumericCellNode = Provenance.dependencyNode
  "paid sparse calibration numeric cell"
  Provenance.dashiFormal
  "target cell promoted only after source identity, same-object manifestation and locator-specific acquisition are paid"
  false

------------------------------------------------------------------------
-- Dependency edges.  Identity/navigation coordinates are retained but are not
-- all marked required for every numeric cell.
------------------------------------------------------------------------

articleToKernel : Provenance.DependencyEdge
articleToKernel = Provenance.dependencyEdge articleNode sparseKernelNode
  Provenance.evidenceRole true
  "article pays source-bounded landscape/state/rate-role premises; DASHI owns the typed kernel construction"

openStructureToKernel : Provenance.DependencyEdge
openStructureToKernel = Provenance.dependencyEdge openStructureNode sparseKernelNode
  Provenance.alignmentRole false
  "required only for open-endpoint structural-reference consumers, not every edge-rate cell"

closedStructureToKernel : Provenance.DependencyEdge
closedStructureToKernel = Provenance.dependencyEdge closedStructureNode sparseKernelNode
  Provenance.alignmentRole false
  "required only for closed-endpoint structural-reference consumers, not every edge-rate cell"

uniprotToKernel : Provenance.DependencyEdge
uniprotToKernel = Provenance.dependencyEdge uniprotNode sparseKernelNode
  Provenance.vocabularyRole false
  "same-protein identity/navigation coordinate; not a numeric calibration payment"

qidToKernel : Provenance.DependencyEdge
qidToKernel = Provenance.dependencyEdge adkQidNode sparseKernelNode
  Provenance.vocabularyRole false
  "supplemental external identity only"

kernelToGuard : Provenance.DependencyEdge
kernelToGuard = Provenance.dependencyEdge sparseKernelNode manifestationGuardNode
  Provenance.residualRole true
  "guard preserves which sparse cells remain unpaid and why"

guardToRuntime : Provenance.DependencyEdge
guardToRuntime = Provenance.dependencyEdge manifestationGuardNode runtimeAcquisitionNode
  Provenance.acquisitionRole true
  "runtime acquisition is admissible only after same-object manifestation and locator requirements are retained"

runtimeToPaidCell : Provenance.DependencyEdge
runtimeToPaidCell = Provenance.dependencyEdge runtimeAcquisitionNode paidNumericCellNode
  Provenance.acquisitionRole true
  "a concrete locator-specific acquisition is required before an unpaid numeric cell may be promoted"

articleToUncertainty : Provenance.DependencyEdge
articleToUncertainty = Provenance.dependencyEdge articleNode uncertaintyNode
  Provenance.evidenceRole true
  "article pays the approximate metadynamics free-energy error statement"

uncertaintyToPaidCell : Provenance.DependencyEdge
uncertaintyToPaidCell = Provenance.dependencyEdge uncertaintyNode paidNumericCellNode
  Provenance.residualRole false
  "required only for a paid BE-META free-energy consumer; does not create the missing value"

calibrationProvenanceGraph : Provenance.TypedDependencyGraph
calibrationProvenanceGraph = Provenance.typedDependencyGraph
  "AdK sparse calibration provenance dependency graph"
  ( articleNode
  ∷ openStructureNode
  ∷ closedStructureNode
  ∷ uniprotNode
  ∷ adkQidNode
  ∷ sparseKernelNode
  ∷ manifestationGuardNode
  ∷ runtimeAcquisitionNode
  ∷ uncertaintyNode
  ∷ paidNumericCellNode
  ∷ [] )
  ( articleToKernel
  ∷ openStructureToKernel
  ∷ closedStructureToKernel
  ∷ uniprotToKernel
  ∷ qidToKernel
  ∷ kernelToGuard
  ∷ guardToRuntime
  ∷ runtimeToPaidCell
  ∷ articleToUncertainty
  ∷ uncertaintyToPaidCell
  ∷ [] )

provenanceLoad : Provenance.ProvenanceLoadSummary
provenanceLoad = Provenance.summarizeProvenanceLoad calibrationProvenanceGraph

------------------------------------------------------------------------
-- Keep canonical source/identity objects live rather than copying strings.
------------------------------------------------------------------------

articleSource = Sparse.liLiuJi2015Source
openStructureSource = Structural.open4AKESource
closedStructureSource = Structural.closed1AKESource
openStructureDoi = Structural.openPdbDoi
closedStructureDoi = Structural.closedPdbDoi
sharedProteinIdentity = Structural.adkUniProt
sharedAdkQid = Structural.adkQid
acquisitionBoundary = Guard.canonicalGuardedCalibrationAcquisitionBoundary
freeEnergyUncertaintyBoundary = Uncertainty.canonicalAdKMetadynamicsUncertaintyBoundary

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data IdentityNodeAlonePaysNumericCell : Set where
data SourceCountCreatesTruthWeight : Set where
data ProvenanceGraphCreatesScientificAuthority : Set where

identityNodeDoesNotPayNumericCell : IdentityNodeAlonePaysNumericCell → ⊥
identityNodeDoesNotPayNumericCell ()

sourceCountDoesNotCreateTruthWeight : SourceCountCreatesTruthWeight → ⊥
sourceCountDoesNotCreateTruthWeight ()

provenanceGraphDoesNotCreateAuthority : ProvenanceGraphCreatesScientificAuthority → ⊥
provenanceGraphDoesNotCreateAuthority ()

record AdKCalibrationProvenanceGraphBoundary : Set where
  constructor adk-calibration-provenance-graph-boundary
  field
    articleSourceRetained : Bool
    structuralSourcesRetained : Bool
    externalIdentityNodesRetained : Bool
    sparseKernelRetained : Bool
    acquisitionGuardRetained : Bool
    uncertaintyEnvelopeRetained : Bool
    numericPromotionRequiresRuntimeAcquisition : Bool
    identityNodeAlonePaysNumericCell : Bool
    sourceCountCreatesTruthWeight : Bool
    provenanceGraphCreatesScientificAuthority : Bool

canonicalAdKCalibrationProvenanceGraphBoundary : AdKCalibrationProvenanceGraphBoundary
canonicalAdKCalibrationProvenanceGraphBoundary =
  adk-calibration-provenance-graph-boundary
    true true true true true true true
    false false false
