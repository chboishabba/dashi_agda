module DASHI.Biology.FunctionalConnectomeBodyMemoryBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.GenomeSensorimotorConnectomeBridge as Genome
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Neuro
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as BrainFMRI
import Ontology.Brain.BrainExtractionSurface as Extraction
import Ontology.Brain.BrainGovernanceProviso as Governance
import Ontology.Brain.BrainInvariantSurface as Invariant

------------------------------------------------------------------------
-- Candidate-only fMRI / connectome / body-memory placement bridge.
--
-- fMRI is treated as a measurement/proxy surface only.
-- The connectome is treated as a structural/functional graph carrier only.
-- The body-memory residual is treated as a cross-fibre mismatch only.
-- No mind-reading, diagnosis, treatment, reverse inference authority, or
-- clinical authority is promoted by this bridge.

data Never : Set where

data FunctionalConnectomeRoute : Set where
  candidateOnlyBridgeRoute : FunctionalConnectomeRoute
  fmriMeasurementRoute : FunctionalConnectomeRoute
  connectomeCarrierRoute : FunctionalConnectomeRoute
  bodyMemoryResidualRoute : FunctionalConnectomeRoute
  reverseInferenceRoute : FunctionalConnectomeRoute
  mindReadingRoute : FunctionalConnectomeRoute
  diagnosisRoute : FunctionalConnectomeRoute
  treatmentRoute : FunctionalConnectomeRoute
  clinicalAuthorityRoute : FunctionalConnectomeRoute

AdmissibleFunctionalConnectomeRoute :
  FunctionalConnectomeRoute →
  Set
AdmissibleFunctionalConnectomeRoute candidateOnlyBridgeRoute = ⊤
AdmissibleFunctionalConnectomeRoute fmriMeasurementRoute = Never
AdmissibleFunctionalConnectomeRoute connectomeCarrierRoute = Never
AdmissibleFunctionalConnectomeRoute bodyMemoryResidualRoute = Never
AdmissibleFunctionalConnectomeRoute reverseInferenceRoute = Never
AdmissibleFunctionalConnectomeRoute mindReadingRoute = Never
AdmissibleFunctionalConnectomeRoute diagnosisRoute = Never
AdmissibleFunctionalConnectomeRoute treatmentRoute = Never
AdmissibleFunctionalConnectomeRoute clinicalAuthorityRoute = Never

reverseInferenceRejected :
  AdmissibleFunctionalConnectomeRoute reverseInferenceRoute →
  Never
reverseInferenceRejected impossible =
  impossible

mindReadingRejected :
  AdmissibleFunctionalConnectomeRoute mindReadingRoute →
  Never
mindReadingRejected impossible =
  impossible

diagnosisRejected :
  AdmissibleFunctionalConnectomeRoute diagnosisRoute →
  Never
diagnosisRejected impossible =
  impossible

treatmentRejected :
  AdmissibleFunctionalConnectomeRoute treatmentRoute →
  Never
treatmentRejected impossible =
  impossible

clinicalAuthorityRejected :
  AdmissibleFunctionalConnectomeRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRejected impossible =
  impossible

data FMRIMeasurementProxyRole : Set where
  proxyMeasurementSurface : FMRIMeasurementProxyRole
  observationProxySurface : FMRIMeasurementProxyRole
  acquisitionProxySurface : FMRIMeasurementProxyRole
  preprocessingProxySurface : FMRIMeasurementProxyRole
  residualAuditProxySurface : FMRIMeasurementProxyRole

data ConnectomeGraphKind : Set where
  structuralGraphCarrier : ConnectomeGraphKind
  functionalGraphCarrier : ConnectomeGraphKind
  alignmentGraphCarrier : ConnectomeGraphKind
  proxyGraphCarrier : ConnectomeGraphKind

data BodyMemoryFibre : Set where
  interoceptiveFibre : BodyMemoryFibre
  proprioceptiveFibre : BodyMemoryFibre
  somaticTraceFibre : BodyMemoryFibre
  autobiographicalTraceFibre : BodyMemoryFibre
  connectomeAlignmentFibre : BodyMemoryFibre
  fMRIProxyFibre : BodyMemoryFibre

data BodyMemoryMismatchKind : Set where
  crossFibreMismatch : BodyMemoryMismatchKind
  noIdentityMap : BodyMemoryMismatchKind
  noReverseInference : BodyMemoryMismatchKind
  noDiagnosticAuthority : BodyMemoryMismatchKind
  noTreatmentAuthority : BodyMemoryMismatchKind
  noClinicalAuthority : BodyMemoryMismatchKind

record FMRIProxySurface : Set₁ where
  constructor fmriProxySurface
  field
    MeasurementContext : Set
    BOLDSignal : Set
    AcquisitionProtocol : Set
    PreprocessingPipeline : Set
    ProxyMap : Set
    ResidualAudit : Set

    measure :
      MeasurementContext →
      BOLDSignal

    preprocess :
      BOLDSignal →
      BOLDSignal

    projectToProxy :
      BOLDSignal →
      ProxyMap

    auditResidual :
      BOLDSignal →
      ResidualAudit

    role :
      FMRIMeasurementProxyRole

    measurementProxyOnly :
      Bool

    measurementProxyOnlyIsTrue :
      measurementProxyOnly ≡ true

    mindReadingAuthorityBlocked :
      Bool

    mindReadingAuthorityBlockedIsFalse :
      mindReadingAuthorityBlocked ≡ false

    diagnosisAuthorityBlocked :
      Bool

    diagnosisAuthorityBlockedIsFalse :
      diagnosisAuthorityBlocked ≡ false

    treatmentAuthorityBlocked :
      Bool

    treatmentAuthorityBlockedIsFalse :
      treatmentAuthorityBlocked ≡ false

    reverseInferenceAuthorityBlocked :
      Bool

    reverseInferenceAuthorityBlockedIsFalse :
      reverseInferenceAuthorityBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    surfaceReading :
      String

open FMRIProxySurface public

record ConnectomeGraphCarrier : Set₁ where
  constructor connectomeGraphCarrier
  field
    Node : Set
    StructuralEdge : Set
    FunctionalEdge : Set
    StructuralWeight : Set
    FunctionalWeight : Set
    StructuralGraph : Set
    FunctionalGraph : Set
    GraphAlignment : Set

    structuralNode :
      StructuralGraph →
      Node

    structuralEdge :
      StructuralGraph →
      Node →
      Node →
      StructuralEdge

    structuralWeight :
      StructuralGraph →
      StructuralEdge →
      StructuralWeight

    functionalEdge :
      FunctionalGraph →
      Node →
      Node →
      FunctionalEdge

    functionalWeight :
      FunctionalGraph →
      FunctionalEdge →
      FunctionalWeight

    graphAlignment :
      StructuralGraph →
      FunctionalGraph →
      GraphAlignment

    structuralCarrier :
      Bool

    structuralCarrierIsTrue :
      structuralCarrier ≡ true

    functionalCarrier :
      Bool

    functionalCarrierIsTrue :
      functionalCarrier ≡ true

    proxyNotIdentity :
      Bool

    proxyNotIdentityIsTrue :
      proxyNotIdentity ≡ true

    graphCarrierReading :
      String

open ConnectomeGraphCarrier public

record BodyMemoryResidualSurface : Set₁ where
  constructor bodyMemoryResidualSurface
  field
    FibreA : BodyMemoryFibre
    FibreB : BodyMemoryFibre
    MismatchKind : BodyMemoryMismatchKind
    ResidualTrace : Set

    residualTrace :
      ResidualTrace

    crossFibreResidual :
      Bool

    crossFibreResidualIsTrue :
      crossFibreResidual ≡ true

    identityMapBlocked :
      Bool

    identityMapBlockedIsFalse :
      identityMapBlocked ≡ false

    reverseInferenceBlocked :
      Bool

    reverseInferenceBlockedIsFalse :
      reverseInferenceBlocked ≡ false

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsFalse :
      diagnosisBlocked ≡ false

    treatmentBlocked :
      Bool

    treatmentBlockedIsFalse :
      treatmentBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    residualReading :
      String

open BodyMemoryResidualSurface public

record FunctionalConnectomeBodyMemoryBridge : Setω where
  field
    fmriBoundary :
      BrainFMRI.BrainConnectomeFMRIObservationBoundary

    fmriBoundaryIsCanonical :
      fmriBoundary ≡ BrainFMRI.canonicalBrainConnectomeFMRIObservationBoundary

    fmriSurface :
      FMRIProxySurface

    connectomeCarrier :
      ConnectomeGraphCarrier

    bodyMemoryResidual :
      BodyMemoryResidualSurface

    brainExtractionSurface :
      Extraction.BrainExtractionSurface

    brainExtractionSurfaceIsCanonical :
      brainExtractionSurface ≡ Extraction.brainExtractionSurface

    brainInvariantSurface :
      Invariant.BrainInvariantSurface

    brainInvariantSurfaceIsCanonical :
      brainInvariantSurface ≡ Invariant.brainInvariantSurface

    brainGovernanceProviso :
      Governance.BrainGovernanceProviso

    genomeBridge :
      Genome.GenomeSensorimotorConnectomeBridge

    genomeBridgeIsCanonical :
      genomeBridge ≡ Genome.canonicalGenomeSensorimotorConnectomeBridge

    neurochemicalBridge :
      Neuro.NeurochemicalBrainCarrierBridge

    neurochemicalBridgeIsCanonical :
      neurochemicalBridge ≡ Neuro.canonicalNeurochemicalBrainCarrierBridge

    route :
      FunctionalConnectomeRoute

    routeIsCandidateOnly :
      route ≡ candidateOnlyBridgeRoute

    routeAdmissible :
      AdmissibleFunctionalConnectomeRoute route

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    mindReadingBlocked :
      Bool

    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsFalse :
      diagnosisBlocked ≡ false

    treatmentBlocked :
      Bool

    treatmentBlockedIsFalse :
      treatmentBlocked ≡ false

    reverseInferenceAuthorityBlocked :
      Bool

    reverseInferenceAuthorityBlockedIsFalse :
      reverseInferenceAuthorityBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    bridgeReading :
      String

open FunctionalConnectomeBodyMemoryBridge public

canonicalFMRIProxySurface : FMRIProxySurface
canonicalFMRIProxySurface =
  fmriProxySurface
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ signal → signal)
    (λ _ → tt)
    (λ _ → tt)
    proxyMeasurementSurface
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "fMRI is recorded here as a measurement and proxy surface only; it does not promote mind-reading, diagnosis, treatment, reverse inference authority, or clinical authority."

canonicalConnectomeGraphCarrier : ConnectomeGraphCarrier
canonicalConnectomeGraphCarrier =
  connectomeGraphCarrier
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ _ _ _ → tt)
    (λ _ _ → tt)
    (λ _ _ _ → tt)
    (λ _ _ → tt)
    (λ _ _ → tt)
    true
    refl
    true
    refl
    true
    refl
    "The connectome is carried as a structural and functional graph proxy: node, edge, weight, and alignment information are recorded without collapsing structure into authority over body memory."

canonicalBodyMemoryResidualSurface : BodyMemoryResidualSurface
canonicalBodyMemoryResidualSurface =
  bodyMemoryResidualSurface
    interoceptiveFibre
    autobiographicalTraceFibre
    crossFibreMismatch
    ⊤
    tt
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Body-memory is represented as a cross-fibre mismatch residual, not as a reverse-inference engine, diagnosis, treatment, or clinical authority."

canonicalFunctionalConnectomeBodyMemoryBridge :
  FunctionalConnectomeBodyMemoryBridge
canonicalFunctionalConnectomeBodyMemoryBridge =
  record
    { fmriBoundary =
        BrainFMRI.canonicalBrainConnectomeFMRIObservationBoundary
    ; fmriBoundaryIsCanonical =
        refl
    ; fmriSurface =
        canonicalFMRIProxySurface
    ; connectomeCarrier =
        canonicalConnectomeGraphCarrier
    ; bodyMemoryResidual =
        canonicalBodyMemoryResidualSurface
    ; brainExtractionSurface =
        Extraction.brainExtractionSurface
    ; brainExtractionSurfaceIsCanonical =
        refl
    ; brainInvariantSurface =
        Invariant.brainInvariantSurface
    ; brainInvariantSurfaceIsCanonical =
        refl
    ; brainGovernanceProviso =
        Governance.brainGovernanceProviso
    ; genomeBridge =
        Genome.canonicalGenomeSensorimotorConnectomeBridge
    ; genomeBridgeIsCanonical =
        refl
    ; neurochemicalBridge =
        Neuro.canonicalNeurochemicalBrainCarrierBridge
    ; neurochemicalBridgeIsCanonical =
        refl
    ; route =
        candidateOnlyBridgeRoute
    ; routeIsCandidateOnly =
        refl
    ; routeAdmissible =
        tt
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; mindReadingBlocked =
        false
    ; mindReadingBlockedIsFalse =
        refl
    ; diagnosisBlocked =
        false
    ; diagnosisBlockedIsFalse =
        refl
    ; treatmentBlocked =
        false
    ; treatmentBlockedIsFalse =
        refl
    ; reverseInferenceAuthorityBlocked =
        false
    ; reverseInferenceAuthorityBlockedIsFalse =
        refl
    ; clinicalAuthorityBlocked =
        false
    ; clinicalAuthorityBlockedIsFalse =
        refl
    ; bridgeReading =
        "Candidate-only bridge for fMRI/connectome/body-memory placement: fMRI stays a proxy measurement surface, the connectome stays a structural/functional graph carrier, and body-memory remains a cross-fibre mismatch residual with mind-reading, diagnosis, treatment, reverse inference authority, and clinical authority blocked."
    }
