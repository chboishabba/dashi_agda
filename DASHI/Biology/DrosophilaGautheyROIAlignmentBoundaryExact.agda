module DASHI.Biology.DrosophilaGautheyROIAlignmentBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Gauthey selected-ROI / source-supervoxel alignment boundary.
--
-- Scientific source:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1;
-- preprocessed data DOI 10.5281/zenodo.17618684;
-- analysis code github:murthylab/lightbead-analysis.
--
-- Corrected source semantics:
-- deposited 940 x 668 = 940 selected ROI rows x 668 time samples.
-- The previously audited 04032024 n2000 labels/ROI list belong to the LBM lane,
-- not the pooled conventional-2p lane used to create this matrix.
------------------------------------------------------------------------

record ROIAlignmentDiagnostic : Set where
  constructor roiAlignmentDiagnostic
  field
    selectedFunctionalROICount : Nat
    timeSampleCount : Nat
    comparedSegmentationLabelCount : Nat
    comparedResponsiveROICount : Nat
    sameCardinality : Bool
    comparisonIsSameAcquisitionLane : Bool
    explicitMappingPresent : Bool
    identityPromotable : Bool
    evidenceKind : String

open ROIAlignmentDiagnostic public

record ROIAlignmentBoundary : Set where
  constructor roiAlignmentBoundary
  field
    timeAxisDoesNotImplyFunctionalUnitCarrier : Bool
    pooled2PDoesNotInheritLBLabelIdentity : Bool
    equalCardinalityDoesNotImplyIdentity : Bool
    contiguousLabelsDoNotImplySelectedROIOrder : Bool
    responsiveSubsetDoesNotImplySelectedROIMap : Bool
    explicitMappingRequiresDomainCoverage : Bool
    explicitMappingRequiresSameLaneSourceIdentity : Bool
    mappedROIStillDoesNotImplyMaleCNSNeuronIdentity : Bool

open ROIAlignmentBoundary public

canonicalROIAlignmentBoundary : ROIAlignmentBoundary
canonicalROIAlignmentBoundary =
  roiAlignmentBoundary true true true true true true true true

-- Runtime diagnostic using the LB companion objects is retained as a negative
-- cross-lane receipt, not as the candidate 2p mapping problem.
legacyCrossLaneDiagnostic : ROIAlignmentDiagnostic
legacyCrossLaneDiagnostic =
  roiAlignmentDiagnostic
    940
    668
    1999
    2967
    false
    false
    false
    false
    "cross-lane diagnostic: pooled 2p selected ROIs compared with LBM n2000 products"

record ExplicitROIMapReceipt : Set where
  constructor explicitROIMapReceipt
  field
    mappingArtifactIdentifier : String
    completeSelectedROIDomain : Bool
    sourceSupervoxelsExist : Bool
    sameAcquisitionLane : Bool
    mappingProvenanceRecoverable : Bool
    sameAnimalIdentityClaimed : Bool

open ExplicitROIMapReceipt public

record ROIMapPromotionAssessment : Set where
  constructor roiMapPromotionAssessment
  field
    mappingPresent : Bool
    domainClosed : Bool
    codomainClosed : Bool
    laneClosed : Bool
    provenanceClosed : Bool
    anatomicalROIIdentityAdmissible : Bool
    neuronIdentityAdmissible : Bool

open ROIMapPromotionAssessment public

canonicalExplicitMapBoundary : ROIMapPromotionAssessment
canonicalExplicitMapBoundary =
  roiMapPromotionAssessment true true true true true true false
