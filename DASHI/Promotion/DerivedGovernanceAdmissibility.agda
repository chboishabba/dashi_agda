module DASHI.Promotion.DerivedGovernanceAdmissibility where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.MeasurementProxyBoundaryCore as Existing

------------------------------------------------------------------------
-- Proposition-level measurement, inference, and authority governance.

data Never : Set where

data MeasurementKind : Set where
  directObservation : MeasurementKind
  processedProxy : MeasurementKind
  latentEstimate : MeasurementKind

data InterpretationKind : Set where
  descriptiveInterpretation : InterpretationKind
  proxyInterpretation : InterpretationKind
  causalInterpretation : InterpretationKind
  diagnosticInterpretation : InterpretationKind
  mindReadingInterpretation : InterpretationKind
  interventionInterpretation : InterpretationKind

data EvidenceKind : Set where
  causalIdentificationEvidence : EvidenceKind
  diagnosticValidationEvidence : EvidenceKind
  interventionValidationEvidence : EvidenceKind

data AdditionalEvidence : EvidenceKind → Set where
  validatedCausalBridge :
    (citationKey : String) →
    AdditionalEvidence causalIdentificationEvidence
  validatedDiagnosticBridge :
    (citationKey : String) →
    AdditionalEvidence diagnosticValidationEvidence
  validatedInterventionBridge :
    (citationKey : String) →
    AdditionalEvidence interventionValidationEvidence

-- Safe interpretations require no promoted authority.
data AdmissibleInterpretation : MeasurementKind → InterpretationKind → Set where
  directMayDescribe :
    AdmissibleInterpretation directObservation descriptiveInterpretation
  proxyMayDescribe :
    AdmissibleInterpretation processedProxy descriptiveInterpretation
  proxyMayRemainProxy :
    AdmissibleInterpretation processedProxy proxyInterpretation
  latentMayRemainProxy :
    AdmissibleInterpretation latentEstimate proxyInterpretation

-- Escalated claims require a typed external evidence bridge.
data EvidenceBackedInterpretation : MeasurementKind → InterpretationKind → Set where
  causalWithEvidence :
    ∀ {measurement} →
    AdditionalEvidence causalIdentificationEvidence →
    EvidenceBackedInterpretation measurement causalInterpretation
  diagnosisWithEvidence :
    ∀ {measurement} →
    AdditionalEvidence diagnosticValidationEvidence →
    EvidenceBackedInterpretation measurement diagnosticInterpretation
  interventionWithEvidence :
    ∀ {measurement} →
    AdditionalEvidence interventionValidationEvidence →
    EvidenceBackedInterpretation measurement interventionInterpretation

proxyDiagnosisBlocked :
  AdmissibleInterpretation processedProxy diagnosticInterpretation → Never
proxyDiagnosisBlocked ()

proxyCausalClosureBlocked :
  AdmissibleInterpretation processedProxy causalInterpretation → Never
proxyCausalClosureBlocked ()

proxyMindReadingBlocked :
  AdmissibleInterpretation processedProxy mindReadingInterpretation → Never
proxyMindReadingBlocked ()

latentMindReadingBlocked :
  AdmissibleInterpretation latentEstimate mindReadingInterpretation → Never
latentMindReadingBlocked ()

diagnosisNeedsEvidence :
  ∀ {measurement} →
  EvidenceBackedInterpretation measurement diagnosticInterpretation →
  AdditionalEvidence diagnosticValidationEvidence
diagnosisNeedsEvidence (diagnosisWithEvidence evidence) = evidence

interventionNeedsEvidence :
  ∀ {measurement} →
  EvidenceBackedInterpretation measurement interventionInterpretation →
  AdditionalEvidence interventionValidationEvidence
interventionNeedsEvidence (interventionWithEvidence evidence) = evidence

safeProxyWitness :
  AdmissibleInterpretation processedProxy proxyInterpretation
safeProxyWitness = proxyMayRemainProxy

existingMeasurementBoundary : Existing.MeasurementProxyBoundary
existingMeasurementBoundary = Existing.canonicalMeasurementProxyBoundary
