module DASHI.Biology.Protein.TRPA1AdKSourceBoundedAcquisitionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact as TRPA1
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact as AdKLedger
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointExact as AdKEndpoint
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationProvenanceGraphExact as AdKProvenance

------------------------------------------------------------------------
-- TRPA1 / ADK SOURCE-BOUNDED ACQUISITION CROSS-POLLINATION
--
-- Purpose: retain the original Feng et al. protein task as the parent protein
-- objective while using the AdK tranche only as a worked acquisition/provenance
-- exemplar.  The reusable pattern is information architecture:
--
--   coarse observation
--     -> separating evidence
--     -> retain missing coordinate/provenance
--     -> source-bounded enriched observation
--     -> consumer-relative use.
--
-- No biological mechanism, numeric value, source authorship, or same-object
-- identity transfers between TRPA1 and adenylate kinase.
------------------------------------------------------------------------

record ProteinAcquisitionInstance : Set where
  constructor protein-acquisition-instance
  field
    instanceLabel : String
    sourceReference : String
    erasedCoordinate : String
    retainedCoordinate : String
    consumerReference : String
    missingnessPolicy : String
    provenancePolicy : String
open ProteinAcquisitionInstance public

trpa1AcquisitionInstance : ProteinAcquisitionInstance
trpa1AcquisitionInstance = protein-acquisition-instance
  "Feng et al. TRPA1 single-residue thermal-adaptation instance"
  "Science Advances 2026; DOI 10.1126/sciadv.aee3948"
  "protein identity alone"
  "protein identity + pore-residue state"
  "thermal-response discrimination in the source-bounded comparative/mutational system"
  "missing residue state may not be inferred from the protein name"
  "article identity and source receipt bound the empirical premise; DASHI owns the finite non-factorability/repair formalisation"

adkAcquisitionInstance : ProteinAcquisitionInstance
adkAcquisitionInstance = protein-acquisition-instance
  "Li-Liu-Ji adenylate-kinase sparse calibration instance"
  "Biophysical Journal 2015; DOI 10.1016/j.bpj.2015.06.059"
  "state/edge identity without a paid numeric cell"
  "state/edge role + coordinate role + source locator + payment status + method/uncertainty"
  "query-relative geometric/free-energy/Kramers calibration"
  "unpaid numeric cells remain explicit and cannot be inferred from endpoints, neighboring states, source identity, or uncertainty"
  "DOI/PMID/PMCID/PDB/UniProt/QID are provenance coordinates; locator-specific source payment is still required for each promoted numeric cell"

------------------------------------------------------------------------
-- Existing donors remain authoritative only for their own domains.
------------------------------------------------------------------------

trpa1Boundary : TRPA1.TRPA1ThermalAdaptationBoundary
trpa1Boundary = TRPA1.canonicalTRPA1ThermalAdaptationBoundary

adkLedgerBoundary : AdKLedger.AdKCalibrationPaymentLedgerBoundary
adkLedgerBoundary = AdKLedger.canonicalAdKCalibrationPaymentLedgerBoundary

adkEndpointBoundary : AdKEndpoint.SourcePaidThreeCVEndpointBoundary
adkEndpointBoundary = AdKEndpoint.canonicalSourcePaidThreeCVEndpointBoundary

adkProvenanceBoundary : AdKProvenance.AdKCalibrationProvenanceGraphBoundary
adkProvenanceBoundary = AdKProvenance.canonicalAdKCalibrationProvenanceGraphBoundary

------------------------------------------------------------------------
-- Shared theorem shape is structural, not same-object.
------------------------------------------------------------------------

record SharedAcquisitionShape : Set where
  constructor shared-acquisition-shape
  field
    coarseObservationMayEraseConsumerRelevantCoordinate : Bool
    separatingEvidenceRequiresRetainedCoordinate : Bool
    enrichedObservationRetainsSourceRole : Bool
    missingCoordinateRemainsExplicit : Bool
    sourceIdentityAloneCreatesDomainClaim : Bool
    crossDomainSimilarityCreatesSameObject : Bool
open SharedAcquisitionShape public

canonicalSharedAcquisitionShape : SharedAcquisitionShape
canonicalSharedAcquisitionShape = shared-acquisition-shape
  true true true true false false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data AdKNumericsCreateTRPA1ThermalMechanism : Set where
data TRPA1ResidueCreatesAdKTransitionKernel : Set where
data SharedProteinArchitectureCreatesSameObject : Set where
data CrossPollinationTransfersSourceAuthorship : Set where

adkNumericsDoNotCreateTRPA1Mechanism : AdKNumericsCreateTRPA1ThermalMechanism → ⊥
adkNumericsDoNotCreateTRPA1Mechanism ()

trpa1ResidueDoesNotCreateAdKKernel : TRPA1ResidueCreatesAdKTransitionKernel → ⊥
trpa1ResidueDoesNotCreateAdKKernel ()

sharedArchitectureDoesNotCreateSameObject : SharedProteinArchitectureCreatesSameObject → ⊥
sharedArchitectureDoesNotCreateSameObject ()

crossPollinationDoesNotTransferAuthorship : CrossPollinationTransfersSourceAuthorship → ⊥
crossPollinationDoesNotTransferAuthorship ()

------------------------------------------------------------------------
-- Parent-objective boundary.
------------------------------------------------------------------------

record ProteinAcquisitionCrossPollinationBoundary : Set where
  constructor protein-acquisition-cross-pollination-boundary
  field
    trpa1ProteinIdentityAloneInadequate : Bool
    adkEndpointThreeCVPaid : Bool
    adkIntermediateNumericsRemainSparse : Bool
    sourceIdentityRetainedWithoutAuthorityPromotion : Bool
    feng2026OriginalProteinTaskRetained : Bool
    nextParentResidualIsProteinGeneralisation : Bool
    adkNumericsCreateTRPA1ThermalMechanism : Bool
    trpa1ResidueCreatesAdKTransitionKernel : Bool
    sharedProteinArchitectureCreatesSameObject : Bool
    crossPollinationTransfersSourceAuthorship : Bool
    nextResidual : String
open ProteinAcquisitionCrossPollinationBoundary public

canonicalProteinAcquisitionCrossPollinationBoundary : ProteinAcquisitionCrossPollinationBoundary
canonicalProteinAcquisitionCrossPollinationBoundary =
  protein-acquisition-cross-pollination-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    "return to the parent protein programme after this AdK acquisition round: generalise the source-bounded coordinate-retention pattern across protein function/structure/perturbation consumers, using Feng et al. TRPA1 as the original residue-gating instance and AdK only as the numeric/provenance acquisition instance. Do not continue adding AdK-specific layers unless they discharge a concrete unpaid cell or test the generic protein acquisition theorem."
