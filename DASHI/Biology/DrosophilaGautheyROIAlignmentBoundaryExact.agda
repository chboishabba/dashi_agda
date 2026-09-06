module DASHI.Biology.DrosophilaGautheyROIAlignmentBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Gauthey functional-column / segmentation-label alignment boundary.
--
-- Scientific source:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1;
-- preprocessed data DOI 10.5281/zenodo.17618684.
--
-- The deposited aggregate functional matrix has 668 archive-local columns.
-- Separate deposited segmentation and responsive-ROI objects do not by
-- themselves identify those columns with anatomical ROIs.
------------------------------------------------------------------------

record ROIAlignmentDiagnostic : Set where
  constructor roiAlignmentDiagnostic
  field
    functionalColumnCount : Nat
    segmentationLabelCount : Nat
    responsiveROICount : Nat
    sameCardinality : Bool
    labelsContiguousFromOne : Bool
    responsiveROIsSubsetOfLabels : Bool
    explicitMappingPresent : Bool
    identityPromotable : Bool
    evidenceKind : String

open ROIAlignmentDiagnostic public

record ROIAlignmentBoundary : Set where
  constructor roiAlignmentBoundary
  field
    equalCardinalityDoesNotImplyIdentity : Bool
    contiguousLabelsDoNotImplyColumnOrder : Bool
    responsiveSubsetDoesNotImplyColumnMap : Bool
    segmentationLabelDoesNotImplyFunctionalUnit : Bool
    explicitMappingRequiresDomainCoverage : Bool
    explicitMappingRequiresExistingLabels : Bool
    mappedCentroidStillDoesNotImplyNeuronIdentity : Bool

open ROIAlignmentBoundary public

canonicalROIAlignmentBoundary : ROIAlignmentBoundary
canonicalROIAlignmentBoundary =
  roiAlignmentBoundary true true true true true true true

unregistered668Diagnostic : ROIAlignmentDiagnostic
unregistered668Diagnostic =
  roiAlignmentDiagnostic
    668
    0
    2967
    false
    false
    false
    false
    false
    "archive-column/ROI relationship unresolved; cardinality/domain checks are diagnostic only"

record ExplicitROIMapReceipt : Set where
  constructor explicitROIMapReceipt
  field
    mappingArtifactIdentifier : String
    completeFunctionalDomain : Bool
    labelsExistInSegmentation : Bool
    mappingProvenanceRecoverable : Bool
    sameAnimalIdentityClaimed : Bool

open ExplicitROIMapReceipt public

record ROIMapPromotionAssessment : Set where
  constructor roiMapPromotionAssessment
  field
    mappingPresent : Bool
    domainClosed : Bool
    codomainClosed : Bool
    provenanceClosed : Bool
    anatomicalROIIdentityAdmissible : Bool
    neuronIdentityAdmissible : Bool

open ROIMapPromotionAssessment public

-- A canonical boundary witness: even an explicit anatomical ROI map does not
-- by itself establish MaleCNS neuron identity.
canonicalExplicitMapBoundary : ROIMapPromotionAssessment
canonicalExplicitMapBoundary =
  roiMapPromotionAssessment true true true true true false
