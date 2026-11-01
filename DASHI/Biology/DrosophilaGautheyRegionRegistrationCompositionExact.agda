module DASHI.Biology.DrosophilaGautheyRegionRegistrationCompositionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Composition boundary for the real Gauthey -> region benchmark seam.
--
-- Scientific sources:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1; data DOI 10.5281/zenodo.17618684.
--
-- Bella E. Brezovec et al.,
-- "BIFROST: A method for registering diverse imaging datasets of the
-- Drosophila brain", DOI 10.1073/pnas.2322687121;
-- data DOI 10.5061/dryad.8pk0p2nx1 and DOI 10.5281/zenodo.11097259.
------------------------------------------------------------------------

record FunctionalToLabelReceipt : Set where
  constructor functionalToLabelReceipt
  field
    sourceIdentifier : String
    completeFunctionalDomain : Bool
    labelsExistInSegmentation : Bool
    provenanceRecoverable : Bool

open FunctionalToLabelReceipt public

record LabelToRegionReceipt : Set where
  constructor labelToRegionReceipt
  field
    sourceIdentifier : String
    completeRequiredLabelDomain : Bool
    targetAtlasNamed : Bool
    registrationResidualDefined : Bool
    provenanceRecoverable : Bool

open LabelToRegionReceipt public

record RegionRegistrationComposition : Set where
  constructor regionRegistrationComposition
  field
    functionalLabelPaymentClosed : Bool
    labelRegionPaymentClosed : Bool
    regionRegistrationAdmissible : Bool
    neuronIdentityAdmissible : Bool
    sameAnimalIdentityAdmissible : Bool
    outputEvidenceKind : String

open RegionRegistrationComposition public

canonicalIncompleteComposition : RegionRegistrationComposition
canonicalIncompleteComposition =
  regionRegistrationComposition
    false false false false false
    "no region registration before both mapping payments close"

canonicalClosedRegionOnlyComposition : RegionRegistrationComposition
canonicalClosedRegionOnlyComposition =
  regionRegistrationComposition
    true true true false false
    "explicit functional-column->label + label->atlas-region composition"

record RegionRegistrationBoundary : Set where
  constructor regionRegistrationBoundary
  field
    firstMapAloneDoesNotYieldRegion : Bool
    secondMapAloneDoesNotYieldFunctionalRegistration : Bool
    completeJoinRequired : Bool
    regionRegistrationDoesNotYieldNeuronIdentity : Bool
    regionRegistrationDoesNotYieldSameAnimalIdentity : Bool
    residualAndProvenanceRemainSeparateCoordinates : Bool

open RegionRegistrationBoundary public

canonicalRegionRegistrationBoundary : RegionRegistrationBoundary
canonicalRegionRegistrationBoundary =
  regionRegistrationBoundary true true true true true true
