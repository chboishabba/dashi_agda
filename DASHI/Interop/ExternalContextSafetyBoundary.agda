module DASHI.Interop.ExternalContextSafetyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.WikidataCandidateRoleBridge as Wikidata
import DASHI.Interop.WikidataSpectralPressureBridge as SpectralPressure

------------------------------------------------------------------------
-- External-context safety laws.
--
-- This module is the formal boundary for a future runtime world-model
-- compiler.  It intentionally does not implement Wikibase retrieval, P31/P279
-- traversal, closure, cohort induction, or domain-pressure execution.  Those
-- operational facts must arrive as bounded, receipt-backed inputs.

------------------------------------------------------------------------
-- An external identity remains candidate-only until a separate local PNF
-- assignment exists.

externalIdentityDoesNotEntailLocalRole :
  (candidate : Wikidata.WikidataCandidateSurface) →
  Wikidata.candidateIdentityFormalRoleEntailment
    (Wikidata.wikidataEntity candidate)
  ≡
  Wikidata.noFormalRoleEntailed
externalIdentityDoesNotEntailLocalRole candidate =
  refl

externalIdentityHasNoTypedAuthority :
  (candidate : Wikidata.WikidataCandidateSurface) →
  Wikidata.uncommittedCandidateAuthority candidate
  ≡
  Wikidata.noTypedTermAuthority
externalIdentityHasNoTypedAuthority candidate =
  Wikidata.uncommittedCandidateHasNoAuthority candidate

------------------------------------------------------------------------
-- Coverage is a first-class boundary.  A bounded graph frontier or omitted
-- property never becomes an observed absence.

data CoverageStatus : Set where
  coverageComplete : CoverageStatus
  coverageIncomplete : CoverageStatus
  propertyNotInspected : CoverageStatus
  observationInvalid : CoverageStatus

data ReviewDisposition : Set where
  reviewMayProceed : ReviewDisposition
  abstainForCoverage : ReviewDisposition
  abstainForInvalidObservation : ReviewDisposition

dispositionForCoverage :
  CoverageStatus →
  ReviewDisposition
dispositionForCoverage coverageComplete =
  reviewMayProceed
dispositionForCoverage coverageIncomplete =
  abstainForCoverage
dispositionForCoverage propertyNotInspected =
  abstainForCoverage
dispositionForCoverage observationInvalid =
  abstainForInvalidObservation

coverageIncompleteImpliesAbstain :
  dispositionForCoverage coverageIncomplete ≡ abstainForCoverage
coverageIncompleteImpliesAbstain =
  refl

propertyNotInspectedImpliesAbstain :
  dispositionForCoverage propertyNotInspected ≡ abstainForCoverage
propertyNotInspectedImpliesAbstain =
  refl

invalidObservationImpliesAbstain :
  dispositionForCoverage observationInvalid ≡ abstainForInvalidObservation
invalidObservationImpliesAbstain =
  refl

------------------------------------------------------------------------
-- Pressure is diagnostic.  An explicit policy authority is the only owner of
-- an operational consequence, and the default is deliberately unevaluated.

data PressureKind : Set where
  noDiagnosticPressure : PressureKind
  structuralDiagnosticPressure : PressureKind
  spectralDiagnosticPressure : PressureKind

data PolicyAuthority : Set where
  noPolicyAuthority : PolicyAuthority
  explicitPolicyAuthority : String → PolicyAuthority

data PromotionEffect : Set where
  promotionNotEvaluated : PromotionEffect
  policyApplied : PromotionEffect

promotionEffect :
  PolicyAuthority →
  PressureKind →
  PromotionEffect
promotionEffect noPolicyAuthority pressure =
  promotionNotEvaluated
promotionEffect (explicitPolicyAuthority policyRef) noDiagnosticPressure =
  policyApplied
promotionEffect (explicitPolicyAuthority policyRef) structuralDiagnosticPressure =
  policyApplied
promotionEffect (explicitPolicyAuthority policyRef) spectralDiagnosticPressure =
  policyApplied

pressureWithoutPolicyHasNoPromotionEffect :
  (pressure : PressureKind) →
  promotionEffect noPolicyAuthority pressure ≡ promotionNotEvaluated
pressureWithoutPolicyHasNoPromotionEffect noDiagnosticPressure =
  refl
pressureWithoutPolicyHasNoPromotionEffect structuralDiagnosticPressure =
  refl
pressureWithoutPolicyHasNoPromotionEffect spectralDiagnosticPressure =
  refl

spectralWitnessIsDiagnosticPressure :
  SpectralPressure.WikidataSpectralPressureWitness →
  PressureKind
spectralWitnessIsDiagnosticPressure witness =
  spectralDiagnosticPressure

spectralWitnessNeedsPolicyForOperationalEffect :
  (witness : SpectralPressure.WikidataSpectralPressureWitness) →
  promotionEffect noPolicyAuthority
    (spectralWitnessIsDiagnosticPressure witness)
  ≡
  promotionNotEvaluated
spectralWitnessNeedsPolicyForOperationalEffect witness =
  refl

------------------------------------------------------------------------
-- A cohort-derived signature or a contradiction report may guide review, but
-- neither is a repair operation.  This keeps future DSP and P2738/P11260
-- diagnostics from acquiring mutation authority by construction.

record CohortSignatureNonAuthority : Set where
  constructor cohortSignatureNonAuthority
  field
    cohortReference : String
    signatureReference : String
    signatureIsDiagnosticOnly : Bool
    signatureIsDiagnosticOnlyIsTrue : signatureIsDiagnosticOnly ≡ true
    signatureAssignsTruth : Bool
    signatureAssignsTruthIsFalse : signatureAssignsTruth ≡ false
    signaturePromotesCandidate : Bool
    signaturePromotesCandidateIsFalse : signaturePromotesCandidate ≡ false

open CohortSignatureNonAuthority public

record DiagnosticContradictionNoAutomaticRepair : Set where
  constructor diagnosticContradictionNoAutomaticRepair
  field
    contradictionReference : String
    coverage : CoverageStatus
    reviewDisposition : ReviewDisposition
    reviewDispositionMatchesCoverage :
      reviewDisposition ≡ dispositionForCoverage coverage
    automaticRepair : Bool
    automaticRepairIsFalse : automaticRepair ≡ false
    editAuthority : Bool
    editAuthorityIsFalse : editAuthority ≡ false

open DiagnosticContradictionNoAutomaticRepair public

diagnosticContradictionDoesNotRepair :
  (report : DiagnosticContradictionNoAutomaticRepair) →
  automaticRepair report ≡ false
diagnosticContradictionDoesNotRepair report =
  automaticRepairIsFalse report

diagnosticContradictionHasNoEditAuthority :
  (report : DiagnosticContradictionNoAutomaticRepair) →
  editAuthority report ≡ false
diagnosticContradictionHasNoEditAuthority report =
  editAuthorityIsFalse report

------------------------------------------------------------------------
-- Stable compact reading for adapters and generated receipts.

externalContextSafetyStatement : String
externalContextSafetyStatement =
  "External identity does not entail a local role or typed authority. Incomplete, uninspected, and invalid bounded observations abstain. Structural and spectral pressure are diagnostic only; without explicit policy authority they have no promotion effect. Cohort signatures and contradiction reports have no truth, edit, or automatic-repair authority."
