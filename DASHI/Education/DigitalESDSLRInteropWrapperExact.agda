module DASHI.Education.DigitalESDSLRInteropWrapperExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- THIN DIGITAL-ESD -> SLR INTEROP WRAPPER
--
-- Application-side only.
--
-- The wrapper owns:
--   * invocation/configuration provenance;
--   * exact Digital-ESD input artifact identity;
--   * returned SLR manifest/receipt identity;
--   * same-object reconciliation;
--   * candidate/non-promotion verification.
--
-- It does NOT own:
--   * document parsing semantics;
--   * canonical SLR evidence semantics;
--   * reviewed-evidence reduction;
--   * SourceAuditAdmission;
--   * source/claim truth.
------------------------------------------------------------------------

record SLRInteropInvocationReceipt : Set where
  constructor slr-interop-invocation-receipt
  field
    wrapperReference : String
    wrapperVersionReference : String

    inputManifestReference : String
    inputManifestSha256 : String

    externalToolReference : String
    externalToolRevisionReference : String
    invocationReference : String

    outputManifestReference : String
    outputManifestSha256 : String

    sourceIdentityReconciled : Bool
    sourceIdentityReconciledIsTrue :
      sourceIdentityReconciled ≡ true

    sourceRevisionReconciled : Bool
    sourceRevisionReconciledIsTrue :
      sourceRevisionReconciled ≡ true

    contentDigestReconciled : Bool
    contentDigestReconciledIsTrue :
      contentDigestReconciled ≡ true

    candidateOnlyVerified : Bool
    candidateOnlyVerifiedIsTrue :
      candidateOnlyVerified ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open SLRInteropInvocationReceipt public

record DigitalESDSLRInteropBoundary : Set where
  constructor digital-esd-slr-interop-boundary
  field
    applicationWrapperOnly : Bool
    applicationWrapperOnlyIsTrue :
      applicationWrapperOnly ≡ true

    configuredExternalCapability : Bool
    configuredExternalCapabilityIsTrue :
      configuredExternalCapability ≡ true

    hardCodesSLRInternalSourcePaths : Bool
    hardCodesSLRInternalSourcePathsIsFalse :
      hardCodesSLRInternalSourcePaths ≡ false

    wrapperIsProductionSemanticABI : Bool
    wrapperIsProductionSemanticABIIsFalse :
      wrapperIsProductionSemanticABI ≡ false

    wrapperCreatesAdmission : Bool
    wrapperCreatesAdmissionIsFalse :
      wrapperCreatesAdmission ≡ false

    wrapperCreatesTruth : Bool
    wrapperCreatesTruthIsFalse :
      wrapperCreatesTruth ≡ false

open DigitalESDSLRInteropBoundary public

canonicalDigitalESDSLRInteropBoundary : DigitalESDSLRInteropBoundary
canonicalDigitalESDSLRInteropBoundary =
  digital-esd-slr-interop-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

data InteropWrapperCreatesSourceAuditAdmission : Set where
data InteropWrapperCreatesSourceTruth : Set where
data InteropWrapperBecomesProductionSemanticABI : Set where
data ExternalToolPathCreatesAuthority : Set where
data SuccessfulProcessExitCreatesEvidencePayment : Set where
data UnreconciledOutputMayEnterAudit : Set where

interopWrapperDoesNotCreateSourceAuditAdmission :
  InteropWrapperCreatesSourceAuditAdmission → ⊥
interopWrapperDoesNotCreateSourceAuditAdmission ()

interopWrapperDoesNotCreateSourceTruth :
  InteropWrapperCreatesSourceTruth → ⊥
interopWrapperDoesNotCreateSourceTruth ()

interopWrapperDoesNotBecomeProductionSemanticABI :
  InteropWrapperBecomesProductionSemanticABI → ⊥
interopWrapperDoesNotBecomeProductionSemanticABI ()

externalToolPathDoesNotCreateAuthority :
  ExternalToolPathCreatesAuthority → ⊥
externalToolPathDoesNotCreateAuthority ()

successfulProcessExitDoesNotCreateEvidencePayment :
  SuccessfulProcessExitCreatesEvidencePayment → ⊥
successfulProcessExitDoesNotCreateEvidencePayment ()

unreconciledOutputCannotEnterAudit :
  UnreconciledOutputMayEnterAudit → ⊥
unreconciledOutputCannotEnterAudit ()

digitalESDSLRInteropReading : String
digitalESDSLRInteropReading =
  "Digital-ESD uses a thin application-side interop wrapper around a configured external SLR capability. The wrapper records invocation and artifact provenance, reconciles source identity, source revision and content digest, and verifies candidate/non-promotion flags. It does not hard-code SLR internal source paths, become the production semantic ABI, create truth/applicability, or construct SourceAuditAdmission."
