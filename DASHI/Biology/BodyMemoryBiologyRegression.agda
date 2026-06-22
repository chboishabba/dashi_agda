module DASHI.Biology.BodyMemoryBiologyRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Biology.EpigeneticTemporalRegulationBridge as EpigeneticTemporal
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRIGovernance
import DASHI.Biology.LongitudinalFMRIConnectomeDynamicsBridge as Longitudinal
import DASHI.Biology.InterventionConsentLongitudinalGovernance as Consent
import DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge as Hyperfabric
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as IntersectionalLongitudinal

------------------------------------------------------------------------
-- Body-memory biology regression / registry surface.
--
-- This file is intentionally self-contained.  It records a stable candidate-
-- only registry for the body-memory lane so later bridge modules can import
-- or refine the surface without changing the hard gates in this file.

data BodyMemoryAspect : Set where
  bodyFibresAspect : BodyMemoryAspect
  epigeneticRegulationAspect : BodyMemoryAspect
  epigeneticTemporalRegulationAspect : BodyMemoryAspect
  neuroendocrineImmuneCellSignalAspect : BodyMemoryAspect
  fmriConnectomeProxyAspect : BodyMemoryAspect
  longitudinalFMRIConnectomeDynamicsAspect : BodyMemoryAspect
  developmentalWindowAspect : BodyMemoryAspect
  interventionConsentAspect : BodyMemoryAspect
  hyperfabricIntersectionalAspect : BodyMemoryAspect
  brainDnaRepresentationAspect : BodyMemoryAspect
  clinicalGovernanceGatesAspect : BodyMemoryAspect

data BodyMemoryCandidateForm : Set where
  fibreNetworkCandidate : BodyMemoryCandidateForm
  epigeneticStateCandidate : BodyMemoryCandidateForm
  temporalRegulationCandidate : BodyMemoryCandidateForm
  signallingMeshCandidate : BodyMemoryCandidateForm
  imagingProxyCandidate : BodyMemoryCandidateForm
  longitudinalTrajectoryCandidate : BodyMemoryCandidateForm
  developmentalWindowCandidate : BodyMemoryCandidateForm
  consentGovernanceCandidate : BodyMemoryCandidateForm
  hyperfabricInterpretiveCandidate : BodyMemoryCandidateForm
  representationGraphCandidate : BodyMemoryCandidateForm
  governanceBoundaryCandidate : BodyMemoryCandidateForm

data ClinicalBoundaryGate : Set where
  candidateOnlyGate : ClinicalBoundaryGate
  noDiagnosisGate : ClinicalBoundaryGate
  noTreatmentGate : ClinicalBoundaryGate
  noClinicalAuthorityGate : ClinicalBoundaryGate

data GovernanceStatus : Set where
  registryCandidateStatus : GovernanceStatus
  registryNonClinicalStatus : GovernanceStatus
  registryNoAuthorityStatus : GovernanceStatus

data MemoryTraceClaim : Set where
  tissueSupportTrace : MemoryTraceClaim
  chromatinTrace : MemoryTraceClaim
  temporalRegulationTrace : MemoryTraceClaim
  signallingTrace : MemoryTraceClaim
  proxyTrace : MemoryTraceClaim
  longitudinalTrace : MemoryTraceClaim
  developmentalWindowTrace : MemoryTraceClaim
  consentTrace : MemoryTraceClaim
  hyperfabricTrace : MemoryTraceClaim
  representationTrace : MemoryTraceClaim
  gateTrace : MemoryTraceClaim

record BodyMemoryRegistryRow : Set where
  constructor mkBodyMemoryRegistryRow
  field
    rowIndex : Nat
    rowAspect : BodyMemoryAspect
    rowLabel : String
    rowClaim : String
    rowForm : BodyMemoryCandidateForm
    rowTrace : MemoryTraceClaim
    rowBoundaryGates : List ClinicalBoundaryGate
    rowGovernanceStatus : GovernanceStatus
    rowNotes : List String

open BodyMemoryRegistryRow public

record CandidateOnlyReceipt : Set where
  constructor mkCandidateOnlyReceipt
  field
    receiptLabel : String
    receiptAspect : BodyMemoryAspect
    receiptCandidateOnly : Bool
    receiptCandidateOnlyIsTrue : receiptCandidateOnly ≡ true
    receiptNoDiagnosis : Bool
    receiptNoDiagnosisIsFalse : receiptNoDiagnosis ≡ false
    receiptNoTreatment : Bool
    receiptNoTreatmentIsFalse : receiptNoTreatment ≡ false
    receiptNoClinicalAuthority : Bool
    receiptNoClinicalAuthorityIsFalse :
      receiptNoClinicalAuthority ≡ false
    receiptRowsAreStable : List String

open CandidateOnlyReceipt public

record BodyMemoryRegistry : Setω where
  constructor mkBodyMemoryRegistry
  field
    registryLabel : String
    registryVersion : String
    registryRows : List BodyMemoryRegistryRow
    registryReceipts : List CandidateOnlyReceipt
    epigeneticTemporalRegulationBridge :
      EpigeneticTemporal.EpigeneticTemporalRegulationBridge
    epigeneticTemporalRegulationBridgeIsCanonical :
      Bool
    fMRIConnectomeProxyGovernance :
      FMRIGovernance.FMRIConnectomeProxyGovernance
    fMRIConnectomeProxyGovernanceIsCanonical :
      Bool
    longitudinalFMRIConnectomeDynamicsGovernance :
      Longitudinal.LongitudinalFMRIConnectomeDynamicsGovernance
    longitudinalFMRIConnectomeDynamicsGovernanceIsCanonical :
      Bool
    interventionConsentLongitudinalGovernance :
      Consent.InterventionConsentLongitudinalGovernance
    interventionConsentLongitudinalGovernanceIsCanonical :
      Bool
    hyperfabricIntersectionalBodyMemoryBridge :
      Hyperfabric.HyperfabricIntersectionalBodyMemoryBridge
    hyperfabricIntersectionalBodyMemoryBridgeIsCanonical :
      Bool
    intersectionalLongitudinalResidualDynamics :
      IntersectionalLongitudinal.IntersectionalLongitudinalResidualDynamics
    intersectionalLongitudinalResidualDynamicsIsCanonical :
      Bool
    registryBoundarySummary : List String
    registryCandidateOnly : Bool
    registryCandidateOnlyIsTrue : registryCandidateOnly ≡ true
    registryNoDiagnosis : Bool
    registryNoDiagnosisIsFalse : registryNoDiagnosis ≡ false
    registryNoTreatment : Bool
    registryNoTreatmentIsFalse : registryNoTreatment ≡ false
    registryNoClinicalAuthority : Bool
    registryNoClinicalAuthorityIsFalse :
      registryNoClinicalAuthority ≡ false
    registryStableReferenceOnly : Bool
    registryStableReferenceOnlyIsTrue :
      registryStableReferenceOnly ≡ true

open BodyMemoryRegistry public

bodyFibreRow : BodyMemoryRegistryRow
bodyFibreRow =
  mkBodyMemoryRegistryRow
    zero
    bodyFibresAspect
    "body fibres"
    "candidate registry row for connective, fascial, and fibre-network structure"
    fibreNetworkCandidate
    tissueSupportTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "self-contained lane placeholder"
    ∷ "candidate only, not a diagnosis or treatment claim"
    ∷ "no clinical authority encoded"
    ∷ []
    )

epigeneticRegulationRow : BodyMemoryRegistryRow
epigeneticRegulationRow =
  mkBodyMemoryRegistryRow
    (suc zero)
    epigeneticRegulationAspect
    "epigenetic regulation"
    "candidate registry row for chromatin and regulatory-state transport"
    epigeneticStateCandidate
    chromatinTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "registry placeholder for later bridge imports"
    ∷ "candidate-only receipt surface"
    ∷ "no mechanistic clinical authority claimed"
    ∷ []
    )

epigeneticTemporalRegulationRow : BodyMemoryRegistryRow
epigeneticTemporalRegulationRow =
  mkBodyMemoryRegistryRow
    (suc (suc zero))
    epigeneticTemporalRegulationAspect
    "epigenetic temporal regulation"
    "candidate registry row for time-indexed epigenetic regulation and association-only state"
    temporalRegulationCandidate
    temporalRegulationTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "epigenetic time-indexing is recorded as a candidate-only row"
    ∷ "association remains distinct from causation"
    ∷ "no trauma proof or inherited destiny claim is promoted"
    ∷ []
    )

neuroendocrineImmuneCellSignalRow : BodyMemoryRegistryRow
neuroendocrineImmuneCellSignalRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc zero)))
    neuroendocrineImmuneCellSignalAspect
    "neuroendocrine / immune / cell signalling"
    "candidate registry row for coupled endocrine, immune, and cell-signalling proxies"
    signallingMeshCandidate
    signallingTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "signalling coupling is represented as a registry candidate"
    ∷ "no disease, dose, or therapeutic interpretation"
    ∷ "hard gates remain fail-closed"
    ∷ []
    )

fmriConnectomeProxyRow : BodyMemoryRegistryRow
fmriConnectomeProxyRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc zero))))
    fmriConnectomeProxyAspect
    "fMRI / connectome proxy"
    "candidate registry row for imaging-derived proxy structure, not direct brain-state authority"
    imagingProxyCandidate
    proxyTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryNonClinicalStatus
    ( "fMRI and connectome are treated as proxy carriers only"
    ∷ "no diagnostic inference is promoted here"
    ∷ "no clinical authority is conferred"
    ∷ []
    )

longitudinalFMRIConnectomeDynamicsRow : BodyMemoryRegistryRow
longitudinalFMRIConnectomeDynamicsRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc (suc zero)))))
    longitudinalFMRIConnectomeDynamicsAspect
    "longitudinal fMRI / connectome dynamics"
    "candidate registry row for longitudinal session trajectories and residual drift"
    longitudinalTrajectoryCandidate
    longitudinalTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryNonClinicalStatus
    ( "longitudinal proxy trajectories remain candidate-only"
    ∷ "reverse inference and hidden-chart recovery stay blocked in the imported bridge"
    ∷ "fMRI/connectome longitudinal placement is treated as a proxy lane"
    ∷ []
    )

developmentalWindowRow : BodyMemoryRegistryRow
developmentalWindowRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc (suc (suc zero))))))
    developmentalWindowAspect
    "developmental window"
    "candidate registry row for developmental windows and plasticity/pruning proxies"
    developmentalWindowCandidate
    developmentalWindowTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "developmental windows are tracked as candidate contexts only"
    ∷ "plasticity and pruning remain proxy vocabulary"
    ∷ "DNA destiny and critical-period determinism are not promoted"
    ∷ []
    )

interventionConsentRow : BodyMemoryRegistryRow
interventionConsentRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    interventionConsentAspect
    "intervention / consent"
    "candidate registry row for pacing, consent, review, and safety-seed governance"
    consentGovernanceCandidate
    consentTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryNoAuthorityStatus
    ( "consent and pacing stay explicitly longitudinal"
    ∷ "forced disclosure and therapeutic authority remain blocked in the imported governance bridge"
    ∷ "the safety seed is governance, not treatment or cure"
    ∷ []
    )

hyperfabricIntersectionalRow : BodyMemoryRegistryRow
hyperfabricIntersectionalRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    hyperfabricIntersectionalAspect
    "hyperfabric / intersectional"
    "candidate registry row for hyperfabric interpretive carriers and axis auditing"
    hyperfabricInterpretiveCandidate
    hyperfabricTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "dialectic and hyperfabric vocabulary remain candidate interpretive material"
    ∷ "social truth, legal authority, and educational authority are not promoted"
    ∷ "intersectional longitudinal residual dynamics remain a residual gap surface"
    ∷ []
    )

brainDnaRepresentationRow : BodyMemoryRegistryRow
brainDnaRepresentationRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    brainDnaRepresentationAspect
    "BrainDNA representation"
    "candidate registry row for symbolic brain-DNA representation, not causal identity"
    representationGraphCandidate
    representationTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryCandidateStatus
    ( "representation only, not genotype-to-phenotype authority"
    ∷ "no treatment or diagnosis semantics attached"
    ∷ "stable placeholder for future imported bridges"
    ∷ []
    )

clinicalGovernanceGatesRow : BodyMemoryRegistryRow
clinicalGovernanceGatesRow =
  mkBodyMemoryRegistryRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    clinicalGovernanceGatesAspect
    "clinical governance gates"
    "candidate registry row encoding explicit fail-closed clinical boundaries"
    governanceBoundaryCandidate
    gateTrace
    ( candidateOnlyGate
    ∷ noDiagnosisGate
    ∷ noTreatmentGate
    ∷ noClinicalAuthorityGate
    ∷ []
    )
    registryNoAuthorityStatus
    ( "clinical governance stays candidate only"
    ∷ "no diagnosis, no treatment, no authority"
    ∷ "registry is reference-only"
    ∷ []
    )

canonicalBodyMemoryRegistryRows : List BodyMemoryRegistryRow
canonicalBodyMemoryRegistryRows =
  bodyFibreRow
  ∷ epigeneticRegulationRow
  ∷ epigeneticTemporalRegulationRow
  ∷ neuroendocrineImmuneCellSignalRow
  ∷ fmriConnectomeProxyRow
  ∷ longitudinalFMRIConnectomeDynamicsRow
  ∷ developmentalWindowRow
  ∷ interventionConsentRow
  ∷ hyperfabricIntersectionalRow
  ∷ brainDnaRepresentationRow
  ∷ clinicalGovernanceGatesRow
  ∷ []

bodyFibreReceipt : CandidateOnlyReceipt
bodyFibreReceipt =
  mkCandidateOnlyReceipt
    "body fibres candidate-only receipt"
    bodyFibresAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "fibre-network row held in candidate-only form"
    ∷ "no diagnosis, treatment, or authority gates are open"
    ∷ []
    )

epigeneticRegulationReceipt : CandidateOnlyReceipt
epigeneticRegulationReceipt =
  mkCandidateOnlyReceipt
    "epigenetic regulation candidate-only receipt"
    epigeneticRegulationAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "epigenetic row is a registry candidate only"
    ∷ "chromatin state is not promoted to clinical authority"
    ∷ []
    )

epigeneticTemporalRegulationReceipt : CandidateOnlyReceipt
epigeneticTemporalRegulationReceipt =
  mkCandidateOnlyReceipt
    "epigenetic temporal regulation candidate-only receipt"
    epigeneticTemporalRegulationAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "time-indexed epigenetic regulation remains candidate-only"
    ∷ "association does not become causation"
    ∷ []
    )

neuroendocrineImmuneCellSignalReceipt : CandidateOnlyReceipt
neuroendocrineImmuneCellSignalReceipt =
  mkCandidateOnlyReceipt
    "neuroendocrine immune cell signalling candidate-only receipt"
    neuroendocrineImmuneCellSignalAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "coupled signalling remains a candidate carrier"
    ∷ "no diagnostic or therapeutic authority claimed"
    ∷ []
    )

fmriConnectomeProxyReceipt : CandidateOnlyReceipt
fmriConnectomeProxyReceipt =
  mkCandidateOnlyReceipt
    "fMRI connectome proxy candidate-only receipt"
    fmriConnectomeProxyAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "imaging proxy is kept non-clinical"
    ∷ "no authority to infer treatment or diagnosis"
    ∷ []
    )

longitudinalFMRIConnectomeDynamicsReceipt : CandidateOnlyReceipt
longitudinalFMRIConnectomeDynamicsReceipt =
  mkCandidateOnlyReceipt
    "longitudinal fMRI connectome dynamics candidate-only receipt"
    longitudinalFMRIConnectomeDynamicsAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "longitudinal scan dynamics remain a proxy carrier"
    ∷ "session trajectories are not hidden chart recovery"
    ∷ []
    )

developmentalWindowReceipt : CandidateOnlyReceipt
developmentalWindowReceipt =
  mkCandidateOnlyReceipt
    "developmental window candidate-only receipt"
    developmentalWindowAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "developmental windows remain candidate contexts"
    ∷ "plasticity and pruning stay proxy vocabulary"
    ∷ []
    )

interventionConsentReceipt : CandidateOnlyReceipt
interventionConsentReceipt =
  mkCandidateOnlyReceipt
    "intervention consent candidate-only receipt"
    interventionConsentAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "consent and pacing remain explicit governance gates"
    ∷ "forced disclosure and therapeutic authority remain blocked"
    ∷ []
    )

hyperfabricIntersectionalReceipt : CandidateOnlyReceipt
hyperfabricIntersectionalReceipt =
  mkCandidateOnlyReceipt
    "hyperfabric intersectional candidate-only receipt"
    hyperfabricIntersectionalAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "hyperfabric and intersectional vocabularies remain interpretive carriers"
    ∷ "no social truth proof, clinical authority, or monoculture compression"
    ∷ []
    )

brainDnaRepresentationReceipt : CandidateOnlyReceipt
brainDnaRepresentationReceipt =
  mkCandidateOnlyReceipt
    "BrainDNA representation candidate-only receipt"
    brainDnaRepresentationAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "symbolic BrainDNA is a registry representation only"
    ∷ "no causal identity or clinical authority is asserted"
    ∷ []
    )

clinicalGovernanceGatesReceipt : CandidateOnlyReceipt
clinicalGovernanceGatesReceipt =
  mkCandidateOnlyReceipt
    "clinical governance gates candidate-only receipt"
    clinicalGovernanceGatesAspect
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "clinical gates are fail-closed by construction"
    ∷ "reference-only, no diagnosis, no treatment, no authority"
    ∷ []
    )

canonicalBodyMemoryRegistryReceipts : List CandidateOnlyReceipt
canonicalBodyMemoryRegistryReceipts =
  bodyFibreReceipt
  ∷ epigeneticRegulationReceipt
  ∷ epigeneticTemporalRegulationReceipt
  ∷ neuroendocrineImmuneCellSignalReceipt
  ∷ fmriConnectomeProxyReceipt
  ∷ longitudinalFMRIConnectomeDynamicsReceipt
  ∷ developmentalWindowReceipt
  ∷ interventionConsentReceipt
  ∷ hyperfabricIntersectionalReceipt
  ∷ brainDnaRepresentationReceipt
  ∷ clinicalGovernanceGatesReceipt
  ∷ []

canonicalBodyMemoryRegistry : BodyMemoryRegistry
canonicalBodyMemoryRegistry =
  mkBodyMemoryRegistry
    "DASHI.Biology.BodyMemoryBiologyRegression"
    "candidate-registry-0"
    canonicalBodyMemoryRegistryRows
    canonicalBodyMemoryRegistryReceipts
    EpigeneticTemporal.canonicalEpigeneticTemporalRegulationBridge
    true
    FMRIGovernance.canonicalFMRIConnectomeProxyGovernance
    true
    Longitudinal.canonicalLongitudinalFMRIConnectomeDynamicsGovernance
    true
    Consent.canonicalInterventionConsentLongitudinalGovernance
    true
    Hyperfabric.canonicalHyperfabricIntersectionalBodyMemoryBridge
    true
    IntersectionalLongitudinal.canonicalIntersectionalLongitudinalResidualDynamics
    true
    ( "candidate only"
    ∷ "no diagnosis"
    ∷ "no treatment"
    ∷ "no clinical authority"
    ∷ "reference only"
    ∷ "epigenetic temporal regulation imported"
    ∷ "fMRI/connectome longitudinal governance imported"
    ∷ "intervention/consent longitudinal governance imported"
    ∷ "hyperfabric intersectional bridge imported"
    ∷ "intersectional longitudinal residual dynamics imported"
    ∷ []
    )
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    true
    refl

canonicalBodyMemoryRegistryCandidateOnly : Bool
canonicalBodyMemoryRegistryCandidateOnly =
  registryCandidateOnly canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryCandidateOnlyIsTrue :
  canonicalBodyMemoryRegistryCandidateOnly ≡ true
canonicalBodyMemoryRegistryCandidateOnlyIsTrue =
  registryCandidateOnlyIsTrue canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryNoDiagnosis : Bool
canonicalBodyMemoryRegistryNoDiagnosis =
  registryNoDiagnosis canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryNoDiagnosisIsFalse :
  canonicalBodyMemoryRegistryNoDiagnosis ≡ false
canonicalBodyMemoryRegistryNoDiagnosisIsFalse =
  registryNoDiagnosisIsFalse canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryNoTreatment : Bool
canonicalBodyMemoryRegistryNoTreatment =
  registryNoTreatment canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryNoTreatmentIsFalse :
  canonicalBodyMemoryRegistryNoTreatment ≡ false
canonicalBodyMemoryRegistryNoTreatmentIsFalse =
  registryNoTreatmentIsFalse canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryNoClinicalAuthority : Bool
canonicalBodyMemoryRegistryNoClinicalAuthority =
  registryNoClinicalAuthority canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryNoClinicalAuthorityIsFalse :
  canonicalBodyMemoryRegistryNoClinicalAuthority ≡ false
canonicalBodyMemoryRegistryNoClinicalAuthorityIsFalse =
  registryNoClinicalAuthorityIsFalse canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryStableReferenceOnly : Bool
canonicalBodyMemoryRegistryStableReferenceOnly =
  registryStableReferenceOnly canonicalBodyMemoryRegistry

canonicalBodyMemoryRegistryStableReferenceOnlyIsTrue :
  canonicalBodyMemoryRegistryStableReferenceOnly ≡ true
canonicalBodyMemoryRegistryStableReferenceOnlyIsTrue =
  registryStableReferenceOnlyIsTrue canonicalBodyMemoryRegistry

canonicalEpigeneticTemporalRegulationBridgeIsCanonical :
  Bool
canonicalEpigeneticTemporalRegulationBridgeIsCanonical =
  epigeneticTemporalRegulationBridgeIsCanonical canonicalBodyMemoryRegistry

canonicalFMRIGovernanceIsCanonical :
  Bool
canonicalFMRIGovernanceIsCanonical =
  fMRIConnectomeProxyGovernanceIsCanonical canonicalBodyMemoryRegistry

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceIsCanonical :
  Bool
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceIsCanonical =
  longitudinalFMRIConnectomeDynamicsGovernanceIsCanonical
    canonicalBodyMemoryRegistry

canonicalInterventionConsentLongitudinalGovernanceIsCanonical :
  Bool
canonicalInterventionConsentLongitudinalGovernanceIsCanonical =
  interventionConsentLongitudinalGovernanceIsCanonical
    canonicalBodyMemoryRegistry

canonicalHyperfabricIntersectionalBodyMemoryBridgeIsCanonical :
  Bool
canonicalHyperfabricIntersectionalBodyMemoryBridgeIsCanonical =
  hyperfabricIntersectionalBodyMemoryBridgeIsCanonical canonicalBodyMemoryRegistry

canonicalIntersectionalLongitudinalResidualDynamicsIsCanonical :
  Bool
canonicalIntersectionalLongitudinalResidualDynamicsIsCanonical =
  intersectionalLongitudinalResidualDynamicsIsCanonical
    canonicalBodyMemoryRegistry

------------------------------------------------------------------------
-- Regression surface.
--
-- This is intentionally lightweight: the module is not proving biology, it
-- is proving that the registry rows and hard gates are present and fail-closed
-- at the surface level.

record BodyMemoryRegressionReceipt : Setω where
  constructor mkBodyMemoryRegressionReceipt
  field
    receiptRows : List BodyMemoryRegistryRow
    receiptRowsAreCanonical : receiptRows ≡ canonicalBodyMemoryRegistryRows
    receiptCandidateReceipts : List CandidateOnlyReceipt
    receiptCandidateReceiptsAreCanonical :
      receiptCandidateReceipts ≡ canonicalBodyMemoryRegistryReceipts
    receiptCandidateOnly : Bool
    receiptCandidateOnlyIsTrue : receiptCandidateOnly ≡ true
    receiptNoDiagnosis : Bool
    receiptNoDiagnosisIsFalse : receiptNoDiagnosis ≡ false
    receiptNoTreatment : Bool
    receiptNoTreatmentIsFalse : receiptNoTreatment ≡ false
    receiptNoClinicalAuthority : Bool
    receiptNoClinicalAuthorityIsFalse :
      receiptNoClinicalAuthority ≡ false

open BodyMemoryRegressionReceipt public

canonicalBodyMemoryRegressionReceipt : BodyMemoryRegressionReceipt
canonicalBodyMemoryRegressionReceipt =
  mkBodyMemoryRegressionReceipt
    canonicalBodyMemoryRegistryRows
    refl
    canonicalBodyMemoryRegistryReceipts
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

bodyMemoryRegressionRowsAreCanonical :
  receiptRows canonicalBodyMemoryRegressionReceipt ≡ canonicalBodyMemoryRegistryRows
bodyMemoryRegressionRowsAreCanonical =
  receiptRowsAreCanonical canonicalBodyMemoryRegressionReceipt

bodyMemoryRegressionReceiptsAreCanonical :
  receiptCandidateReceipts canonicalBodyMemoryRegressionReceipt ≡
  canonicalBodyMemoryRegistryReceipts
bodyMemoryRegressionReceiptsAreCanonical =
  receiptCandidateReceiptsAreCanonical canonicalBodyMemoryRegressionReceipt

bodyMemoryRegressionCandidateOnlyIsTrue :
  receiptCandidateOnly canonicalBodyMemoryRegressionReceipt ≡ true
bodyMemoryRegressionCandidateOnlyIsTrue =
  receiptCandidateOnlyIsTrue canonicalBodyMemoryRegressionReceipt

bodyMemoryRegressionNoDiagnosisIsFalse :
  receiptNoDiagnosis canonicalBodyMemoryRegressionReceipt ≡ false
bodyMemoryRegressionNoDiagnosisIsFalse =
  receiptNoDiagnosisIsFalse canonicalBodyMemoryRegressionReceipt

bodyMemoryRegressionNoTreatmentIsFalse :
  receiptNoTreatment canonicalBodyMemoryRegressionReceipt ≡ false
bodyMemoryRegressionNoTreatmentIsFalse =
  receiptNoTreatmentIsFalse canonicalBodyMemoryRegressionReceipt

bodyMemoryRegressionNoClinicalAuthorityIsFalse :
  receiptNoClinicalAuthority canonicalBodyMemoryRegressionReceipt ≡ false
bodyMemoryRegressionNoClinicalAuthorityIsFalse =
  receiptNoClinicalAuthorityIsFalse canonicalBodyMemoryRegressionReceipt
