module Ontology.ClinicalDiagnostics.DifferentialDiagnosis where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAGMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRAdmissibilityWitness as CRW
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

private
  canonicalBundle : AGMB.AbstractGaugeMatterBundle
  canonicalBundle = CAGMI.canonicalAbstractGaugeMatterBundle

  canonicalRecovery : AGMB.GaugeMatterRecoveryTheorem canonicalBundle
  canonicalRecovery = CAGMI.canonicalGaugeMatterRecoveryTheorem

  canonicalTransport : AGMB.ObservableTransportWitness canonicalBundle
  canonicalTransport = AGMB.GaugeMatterRecoveryTheorem.transport canonicalRecovery

  canonicalDelta : AGMB.TransportedProjectionDeltaWitness canonicalBundle
  canonicalDelta =
    AGMB.GaugeMatterRecoveryTheorem.transportedProjectionDelta canonicalRecovery

data DiagnosticTest : Set where
  transportAudit : DiagnosticTest
  projectionDeltaAudit : DiagnosticTest
  observableRecoveryAudit : DiagnosticTest

selectNextTest : Nat → DiagnosticTest
selectNextTest zero = transportAudit
selectNextTest (suc zero) = projectionDeltaAudit
selectNextTest (suc (suc _)) = observableRecoveryAudit

record CandidateDiagnosis : Setω where
  field
    carrier : AGMB.Carrier canonicalBundle
    transportDelta : AGMB.TransportedProjectionDeltaWitness canonicalBundle
    transportTarget :
      AGMB.ObservableTransportWitness.TargetCarrier
        (AGMB.TransportedProjectionDeltaWitness.transportW transportDelta)
    transportAdmissible :
      AGMB.TransportedProjectionDeltaWitness.admissibleT
        transportDelta
        transportTarget
    evidence : AGMB.Observable canonicalBundle
    evidenceCarrierSound :
      evidence ≡ AGMB.observableOf canonicalBundle carrier
    evidenceTransportSound :
      evidence
        ≡
      AGMB.ObservableTransportWitness.observeTarget
        (AGMB.TransportedProjectionDeltaWitness.transportW transportDelta)
        transportTarget
    projectionAgree :
      AGMB.ObservableTransportWitness.observeTarget
        (AGMB.TransportedProjectionDeltaWitness.transportW transportDelta)
        (AGMB.TransportedProjectionDeltaWitness.projectAT
          transportDelta
          transportTarget)
        ≡
      AGMB.ObservableTransportWitness.observeTarget
        (AGMB.TransportedProjectionDeltaWitness.transportW transportDelta)
        (AGMB.TransportedProjectionDeltaWitness.projectBT
          transportDelta
          transportTarget)
    mdl : Nat

projectEvidenceToCandidate :
  (x : AGMB.Carrier canonicalBundle) →
  SRGOI.shiftRGAdmissible (AGMB.ObservableTransportWitness.transport canonicalTransport x) →
  CandidateDiagnosis
projectEvidenceToCandidate x ax =
  record
    { carrier = x
    ; transportDelta = canonicalDelta
    ; transportTarget = AGMB.ObservableTransportWitness.transport canonicalTransport x
    ; transportAdmissible = ax
    ; evidence = AGMB.observableOf canonicalBundle x
    ; evidenceCarrierSound = refl
    ; evidenceTransportSound =
        AGMB.ObservableTransportWitness.transport-sound
          canonicalTransport
          x
          refl
    ; projectionAgree =
        AGMB.TransportedProjectionDeltaWitness.universalityT
          canonicalDelta
          (AGMB.ObservableTransportWitness.transport canonicalTransport x)
          ax
    ; mdl = AGMB.mdlLevel canonicalBundle x
    }

record AdmissibleDiagnosis : Setω where
  field
    candidate : CandidateDiagnosis
    carrierAdmissible :
      AGMB.admissible canonicalBundle (CandidateDiagnosis.carrier candidate) ≡ true

admissibilityFilter :
  (candidate : CandidateDiagnosis) →
  AGMB.admissible canonicalBundle (CandidateDiagnosis.carrier candidate) ≡ true →
  AdmissibleDiagnosis
admissibilityFilter candidate carrierAdmissible =
  record
    { candidate = candidate
    ; carrierAdmissible = carrierAdmissible
    }

nextTestForCandidate : CandidateDiagnosis → DiagnosticTest
nextTestForCandidate candidate = selectNextTest (CandidateDiagnosis.mdl candidate)

nextTestForDiagnosis : AdmissibleDiagnosis → DiagnosticTest
nextTestForDiagnosis diagnosis =
  nextTestForCandidate (AdmissibleDiagnosis.candidate diagnosis)

canonicalCRDiagnosisCandidate : CandidateDiagnosis
canonicalCRDiagnosisCandidate =
  projectEvidenceToCandidate
    CI.CR
    CRW.canonicalTransportStateCR-shiftRGAdmissible

canonicalCRDiagnosis : AdmissibleDiagnosis
canonicalCRDiagnosis =
  admissibilityFilter canonicalCRDiagnosisCandidate refl

canonicalCRNextTest : DiagnosticTest
canonicalCRNextTest = nextTestForDiagnosis canonicalCRDiagnosis

diagnosisCarrierObservableCompatible :
  ∀ (candidate : CandidateDiagnosis) →
  CandidateDiagnosis.evidence candidate
    ≡
  AGMB.observableOf canonicalBundle (CandidateDiagnosis.carrier candidate)
diagnosisCarrierObservableCompatible candidate =
  CandidateDiagnosis.evidenceCarrierSound candidate

diagnosisTransportObservableCompatible :
  ∀ (candidate : CandidateDiagnosis) →
  CandidateDiagnosis.evidence candidate
    ≡
  AGMB.ObservableTransportWitness.observeTarget
    (AGMB.TransportedProjectionDeltaWitness.transportW
      (CandidateDiagnosis.transportDelta candidate))
    (CandidateDiagnosis.transportTarget candidate)
diagnosisTransportObservableCompatible candidate =
  CandidateDiagnosis.evidenceTransportSound candidate

diagnosisProjectionUniversality :
  ∀ (candidate : CandidateDiagnosis) →
  AGMB.ObservableTransportWitness.observeTarget
    (AGMB.TransportedProjectionDeltaWitness.transportW
      (CandidateDiagnosis.transportDelta candidate))
    (AGMB.TransportedProjectionDeltaWitness.projectAT
      (CandidateDiagnosis.transportDelta candidate)
      (CandidateDiagnosis.transportTarget candidate))
    ≡
  AGMB.ObservableTransportWitness.observeTarget
    (AGMB.TransportedProjectionDeltaWitness.transportW
      (CandidateDiagnosis.transportDelta candidate))
    (AGMB.TransportedProjectionDeltaWitness.projectBT
      (CandidateDiagnosis.transportDelta candidate)
      (CandidateDiagnosis.transportTarget candidate))
diagnosisProjectionUniversality candidate =
  CandidateDiagnosis.projectionAgree candidate

canonicalRecoveredObservable :
  AGMB.Observable canonicalBundle
canonicalRecoveredObservable =
  AGMB.observableOf canonicalBundle CI.CR

canonicalRecoveredObservableTransportSound :
  canonicalRecoveredObservable
    ≡
  AGMB.ObservableTransportWitness.observeTarget canonicalTransport
    (AGMB.ObservableTransportWitness.transport canonicalTransport CI.CR)
canonicalRecoveredObservableTransportSound =
  AGMB.ObservableTransportWitness.transport-sound
    canonicalTransport
    CI.CR
    refl
