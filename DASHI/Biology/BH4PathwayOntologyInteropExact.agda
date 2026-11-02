module DASHI.Biology.BH4PathwayOntologyInteropExact where

open import DASHI.Core.Prelude

import DASHI.Biology.KitzerowBH4SourceRegistry as Kitzerow
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Biology.BH4SystemStateExact as State
import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Core.XPollenationExact as XPollenation
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- BH4 PATHWAY / ONTOLOGY INTEROPERABILITY
--
-- Attribution: Kimberly Kitzerow, "Autism & the Comorbidities Along the BH4
-- Pathway" (2024-01), DOI 10.13140/RG.2.2.23124.37761/1;
-- "The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism
-- and Systemic Comorbidities" (2024-08), ResearchGate 383021907.
-- Existing scientific chemistry is independently owned by Rhea (rhea-db.org),
-- ChEBI (ebi.ac.uk/chebi), and UniProt (uniprot.org).
-- Cross-source model assembly and JSON-LD export are DASHI work.
-- BioPAX Level 3 (biopax.org), GO-CAM (geneontology.org), and SBML Level 3
-- (sbml.org) are future target standards, not completed conformant exports.
------------------------------------------------------------------------

data PathwayAssertionClass : Set where
  creatorHypothesis : PathwayAssertionClass
  sourceCuratedReaction : PathwayAssertionClass
  observedKinetics : PathwayAssertionClass
  ontologyCrossReference : PathwayAssertionClass
  repositoryReconstruction : PathwayAssertionClass

data PathwayExportStatus : Set where
  structuralGraphOnly : PathwayExportStatus
  compartmentBoundModel : PathwayExportStatus
  kineticModel : PathwayExportStatus

currentPathwayExportStatus : PathwayExportStatus
currentPathwayExportStatus = structuralGraphOnly

kitzerowHypothesisSource : Kitzerow.SourceRecord
kitzerowHypothesisSource = Kitzerow.kitzerow2024Allostatic

record TypedPathwayAssertion : Set where
  constructor typed-pathway-assertion
  field
    assertionId : String
    classification : PathwayAssertionClass
    subject : String
    relation : String
    object : String
    sourceLocator : String
    sourceRevision : String
    independentPrimaryVerification : Bool
    biologicalContextPaid : Bool
    quantitativeFluxPaid : Bool
    causalTransitionPaid : Bool

open TypedPathwayAssertion public

-- This is an explicitly candidate-only DASHI transcription. The claim ledger
-- must pin primary source passages before author-level assertion is promoted.
proposedBH4Allocation : TypedPathwayAssertion
proposedBH4Allocation =
  typed-pathway-assertion
    "KIT-PATHWAY-ALLOC-1"
    repositoryReconstruction
    "compartment-specific BH4 pool"
    "proposed resource allocation between"
    "AAAH, NOS and AGMO enzyme branches"
    "DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact; source pin outstanding"
    "Kitzerow ResearchGate 383021907; independently unverified passage"
    false false false false

-- The existing typed BH4 physical system, not this adapter, owns pool state.
sharedSystemStateCarrier : Set
sharedSystemStateCarrier = State.BH4SystemState

-- The existing xPollenation graph owns typed external identifiers and edges.
externalNeighbourhoodCarrier : Set
externalNeighbourhoodCarrier = XPollenation.XPollenationNeighbourhood

-- The existing feasibility checker owns the open-system flux status.
fluxFeasibilityCarrier : Set
fluxFeasibilityCarrier = Flux.BH4JointFluxFeasibility

executedFiniteReactionCount : Nat
executedFiniteReactionCount = Matrix.executedPanelReactionCount

executedFiniteReactionCountExact : executedFiniteReactionCount ≡ 12
executedFiniteReactionCountExact = refl

record PathwayOntologyBoundary : Set where
  constructor pathway-ontology-boundary
  field
    proposedCausalEdgeCreatesCuratedReaction : Bool
    proposedCausalEdgeCreatesCuratedReactionIsFalse :
      proposedCausalEdgeCreatesCuratedReaction ≡ false
    ontologyCrossReferencePaysSameCompartment : Bool
    ontologyCrossReferencePaysSameCompartmentIsFalse :
      ontologyCrossReferencePaysSameCompartment ≡ false
    ontologyCrossReferencePaysKineticRate : Bool
    ontologyCrossReferencePaysKineticRateIsFalse :
      ontologyCrossReferencePaysKineticRate ≡ false
    candidatePathwayGraphCreatesPhysiologicalFlux : Bool
    candidatePathwayGraphCreatesPhysiologicalFluxIsFalse :
      candidatePathwayGraphCreatesPhysiologicalFlux ≡ false
    JSONLDGraphIsAlreadyExecutableSBML : Bool
    JSONLDGraphIsAlreadyExecutableSBMLIsFalse :
      JSONLDGraphIsAlreadyExecutableSBML ≡ false
    partialMechanismConfirmsKitzerowWholeModel : Bool
    partialMechanismConfirmsKitzerowWholeModelIsFalse :
      partialMechanismConfirmsKitzerowWholeModel ≡ false

canonicalPathwayOntologyBoundary : PathwayOntologyBoundary
canonicalPathwayOntologyBoundary =
  pathway-ontology-boundary false refl false refl false refl
    false refl false refl false refl

canonicalPathwayOntologyInteropReceipt : Receipt.GenericReceipt
canonicalPathwayOntologyInteropReceipt =
  Receipt.mkNonPromotingReceipt
    "Kitzerow BH4 pathway/ontology interoperability"
    "DASHI.Biology.BH4PathwayOntologyInteropExact"
    "Kitzerow source registry + canonical 29-by-12 Rhea/ChEBI matrix + typed xPollenation neighbourhoods + shared BH4 system state"
    "adds a source-attributed, structural pathway JSON/JSON-LD exchange surface without inventing an ontology or another physiological flux solver"
    "the exported reaction graph is partial and uncompartmentalized; proposed Kitzerow transitions are separately unverified; no SBML, BioPAX or GO-CAM conformance or kinetic payment is asserted"
    "python3 scripts/check_bh4_pathway_ontology.py"
