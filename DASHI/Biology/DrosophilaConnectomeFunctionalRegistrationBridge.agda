module DASHI.Biology.DrosophilaConnectomeFunctionalRegistrationBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly

------------------------------------------------------------------------
-- Functional imaging becomes scientifically pairable with a connectome only
-- after a receipted registration/identity seam.  Atlas proximity, cell type,
-- morphology and direct identity are kept distinct.
------------------------------------------------------------------------

data RegistrationEvidenceKind : Set where
  atlasRegionOverlap : RegistrationEvidenceKind
  coordinateProximity : RegistrationEvidenceKind
  morphologyAgreement : RegistrationEvidenceKind
  geneticCellTypeAgreement : RegistrationEvidenceKind
  directNeuronIdentity : RegistrationEvidenceKind

data RegistrationBoundary : Set where
  noAtlasRegionEqualsNeuronIdentity : RegistrationBoundary
  noCoordinateProximityEqualsIdentity : RegistrationBoundary
  noFunctionalCorrelationEqualsStructuralEdge : RegistrationBoundary
  noStructuralEdgeEqualsFunctionalCorrelation : RegistrationBoundary
  noRegistrationWithoutResidual : RegistrationBoundary

bifrostSource : Fly.ScientificSourceReceipt
bifrostSource =
  Fly.scientificSourceReceipt
    "Brezovec, Berger, Hao, Lin, Ahmed, Pacheco, Thiberge, Murthy, Clandinin"
    "BIFROST: A method for registering diverse imaging datasets of the Drosophila brain"
    "DOI:10.1073/pnas.2322687121"
    "Functional Drosophila Atlas and registration pipeline for aligning in vivo functional imaging with ex vivo resources including connectomes."

mannSource : Fly.ScientificSourceReceipt
mannSource =
  Fly.scientificSourceReceipt
    "Mann, Gallen, Clandinin"
    "Whole-Brain Calcium Imaging Reveals an Intrinsic Functional Network in Drosophila"
    "DOI:10.1016/j.cub.2017.06.076"
    "Whole-brain calcium imaging with atlas registration in adult Drosophila."

turnerSource : Fly.ScientificSourceReceipt
turnerSource =
  Fly.scientificSourceReceipt
    "Turner, Mann, Clandinin"
    "The connectome predicts resting-state functional connectivity across the Drosophila brain"
    "DOI:10.1016/j.cub.2021.03.004"
    "Relates Drosophila structural connectome connectivity to registered whole-brain functional imaging while retaining structure/function distinction."

registrationSources : List Fly.ScientificSourceReceipt
registrationSources =
  bifrostSource ∷ mannSource ∷ turnerSource ∷ []

record FunctionalConnectomeRegistration : Set₁ where
  field
    FunctionalUnit : Set
    AtlasCoordinate : Set
    ConnectomeUnit : Set
    RegistrationResidual : Set
    Confidence : Set

    functionalCoordinate : FunctionalUnit → AtlasCoordinate
    candidateConnectomeUnit : FunctionalUnit → ConnectomeUnit
    residual : FunctionalUnit → RegistrationResidual
    confidence : FunctionalUnit → Confidence
    evidenceKind : FunctionalUnit → List RegistrationEvidenceKind

    residualAdmissible : RegistrationResidual → Set
    registrationReceipt : Fly.ScientificSourceReceipt

open FunctionalConnectomeRegistration public

record RegisteredFunctionalTrace
    (R : FunctionalConnectomeRegistration) : Set₁ where
  field
    Time : Set
    SignalValue : Set
    functionalUnit : FunctionalUnit R
    signal : Time → SignalValue
    mappedConnectomeUnit : ConnectomeUnit R
    mappingMatchesCandidate :
      mappedConnectomeUnit ≡ candidateConnectomeUnit R functionalUnit

open RegisteredFunctionalTrace public

record StructuralFunctionalComparison
    (R : FunctionalConnectomeRegistration) : Set₁ where
  field
    StructuralWeight : Set
    FunctionalAssociation : Set
    ComparisonResidual : Set

    structuralWeight : ConnectomeUnit R → ConnectomeUnit R → StructuralWeight
    functionalAssociation : FunctionalUnit R → FunctionalUnit R → FunctionalAssociation
    comparisonResidual : StructuralWeight → FunctionalAssociation → ComparisonResidual

    structureEqualsFunctionClaim : Bool
    structureEqualsFunctionClaimIsFalse : structureEqualsFunctionClaim ≡ false

    comparisonReceipt : Fly.ScientificSourceReceipt

open StructuralFunctionalComparison public

canonicalRegistrationBoundaries : List RegistrationBoundary
canonicalRegistrationBoundaries =
  noAtlasRegionEqualsNeuronIdentity
  ∷ noCoordinateProximityEqualsIdentity
  ∷ noFunctionalCorrelationEqualsStructuralEdge
  ∷ noStructuralEdgeEqualsFunctionalCorrelation
  ∷ noRegistrationWithoutResidual
  ∷ []
