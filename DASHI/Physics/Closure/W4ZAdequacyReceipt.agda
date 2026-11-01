module DASHI.Physics.Closure.W4ZAdequacyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W4 Z-peak adequacy receipt surface.
--
-- This module prepares the typed path:
--
--   AcceptedDYLuminosityConventionAuthority
--   -> scripts/run_w4_z_peak_adequacy.py
--   -> W4ZAdequacyReceipt
--
-- The Drell-Yan authority token is constructorless here.  Therefore this
-- lane cannot construct a promoted adequacy receipt, cannot decide pass/fail,
-- and cannot promote W4.

data AcceptedDYLuminosityConventionAuthority : Set where

acceptedDYLuminosityConventionAuthorityMissing :
  AcceptedDYLuminosityConventionAuthority →
  ⊥
acceptedDYLuminosityConventionAuthorityMissing ()

data W4ZAdequacyStatus : Set where
  blockedAwaitingAcceptedDYLuminosityConventionAuthority :
    W4ZAdequacyStatus
  readyToRunAfterAcceptedAuthorityAndRealInputs :
    W4ZAdequacyStatus
  computedAwaitingTypedReviewNoPromotion :
    W4ZAdequacyStatus

data W4ZAdequacyFirstMissing : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    W4ZAdequacyFirstMissing
  missingAcceptedPerBinLuminosityVector :
    W4ZAdequacyFirstMissing
  missingRealZPeakMeasurementPredictionSigmaInputs :
    W4ZAdequacyFirstMissing
  missingTypedAdequacyReviewThreshold :
    W4ZAdequacyFirstMissing

data AcceptedDYLuminosityConventionAuthorityHookState : Set where
  requestedAtCanonicalDefinitionSite :
    AcceptedDYLuminosityConventionAuthorityHookState

data AcceptedDYLuminosityConventionAuthorityHookDisposition : Set where
  failClosedNoConstructorNoProvider :
    AcceptedDYLuminosityConventionAuthorityHookDisposition

w4ZAdequacyFirstMissingBeforeAuthorityHook :
  W4ZAdequacyFirstMissing
w4ZAdequacyFirstMissingBeforeAuthorityHook =
  missingAcceptedDYLuminosityConventionAuthority

w4ZAdequacyFirstMissingAfterAuthorityHook :
  W4ZAdequacyFirstMissing
w4ZAdequacyFirstMissingAfterAuthorityHook =
  missingAcceptedDYLuminosityConventionAuthority

w4ZAdequacyAuthorityHookFirstMissingUnchanged :
  w4ZAdequacyFirstMissingAfterAuthorityHook
  ≡
  w4ZAdequacyFirstMissingBeforeAuthorityHook
w4ZAdequacyAuthorityHookFirstMissingUnchanged =
  refl

record AcceptedDYLuminosityConventionAuthorityPolicyHookRequest : Setω where
  field
    hookState :
      AcceptedDYLuminosityConventionAuthorityHookState

    disposition :
      AcceptedDYLuminosityConventionAuthorityHookDisposition

    canonicalDefinitionSite :
      String

    exactAuthorityName :
      String

    exactReceiptConsumerName :
      String

    firstMissingBeforeHookRequest :
      W4ZAdequacyFirstMissing

    firstMissingAfterHookRequest :
      W4ZAdequacyFirstMissing

    firstMissingUnchanged :
      firstMissingAfterHookRequest
      ≡
      firstMissingBeforeHookRequest

    requiredHookSignature :
      List String

    requiredProviderPacketFields :
      List String

    acceptedOutputContract :
      List String

    tokenProducingHookAuthorizedHere :
      Bool

    tokenProducingHookAuthorizedHereIsFalse :
      tokenProducingHookAuthorizedHere ≡ false

    acceptedAuthorityConstructedHere :
      Bool

    acceptedAuthorityConstructedHereIsFalse :
      acceptedAuthorityConstructedHere ≡ false

    noAcceptedAuthorityHere :
      AcceptedDYLuminosityConventionAuthority →
      ⊥

    failClosedBoundary :
      List String

data W4AuthorityClosureRoute : Set where
  publicSourceSelfIssuedRoute :
    W4AuthorityClosureRoute
  postulateToRecordRewriteRoute :
    W4AuthorityClosureRoute
  localShadowRecordRoute :
    W4AuthorityClosureRoute
  providerOrGovernanceExactHookRoute :
    W4AuthorityClosureRoute

record W4AuthorityClosureRouteAudit : Setω where
  field
    auditedDefinitionSite :
      String

    acceptedRoute :
      W4AuthorityClosureRoute

    rejectedRoutes :
      List W4AuthorityClosureRoute

    publicSourceEvidencePreserved :
      Bool

    publicSourceEvidencePreservedIsTrue :
      publicSourceEvidencePreserved ≡ true

    exactAcceptedAuthorityAvailableHere :
      Bool

    exactAcceptedAuthorityAvailableHereIsFalse :
      exactAcceptedAuthorityAvailableHere ≡ false

    postulateToRecordRewriteAuthorizedHere :
      Bool

    postulateToRecordRewriteAuthorizedHereIsFalse :
      postulateToRecordRewriteAuthorizedHere ≡ false

    noAcceptedAuthorityHere :
      AcceptedDYLuminosityConventionAuthority →
      ⊥

    auditBoundary :
      List String

data W4ZAdequacyFailType : Set where
  acceptedConventionMissing :
    W4ZAdequacyFailType
  thresholdExceeded :
    W4ZAdequacyFailType
  extractionConventionMismatchSuspected :
    W4ZAdequacyFailType
  typedReviewThresholdMissing :
    W4ZAdequacyFailType

data W4ZAdequacyFailCause : Set where
  noAcceptedDYLuminosityConventionAuthority :
    W4ZAdequacyFailCause
  dirtyZPeakChi2PerDofTooLarge :
    W4ZAdequacyFailCause
  likelyExtractionOrConventionMismatch :
    W4ZAdequacyFailCause
  thresholdNotAuthorityBacked :
    W4ZAdequacyFailCause

data W4ZAdequacyResultStatus : Set where
  adequateUnderTypedThreshold :
    W4ZAdequacyResultStatus
  obstructedUnderTypedThreshold :
    W4ZAdequacyResultStatus
  blockedBeforeRun :
    W4ZAdequacyResultStatus

record W4ZAdequacyResult : Set where
  field
    status :
      W4ZAdequacyResultStatus

    artifactSchema :
      String

    chi2PerDof :
      String

    adequacyThreshold :
      String

    adequate :
      Bool

    failType :
      W4ZAdequacyFailType

    failCause :
      W4ZAdequacyFailCause

    resultBoundary :
      List String

canonicalDirtyZPeakObstructedResult :
  W4ZAdequacyResult
canonicalDirtyZPeakObstructedResult =
  record
    { status =
        obstructedUnderTypedThreshold
    ; artifactSchema =
        "dashi-w4-z-peak-adequacy-v1"
    ; chi2PerDof =
        "298.8462841768543"
    ; adequacyThreshold =
        "typed threshold required; do not weaken without authority-backed justification"
    ; adequate =
        false
    ; failType =
        extractionConventionMismatchSuspected
    ; failCause =
        likelyExtractionOrConventionMismatch
    ; resultBoundary =
        "The current dirty Z-peak baseline is a hard negative, not hidden or promoted"
        ∷ "chi2/dof 298.8462841768543 is obstructed under any ordinary adequacy threshold"
        ∷ "The likely cause is extraction/convention mismatch until accepted DY convention and aligned per-bin luminosity inputs are supplied"
        ∷ "Rerun after AcceptedDYLuminosityConventionAuthority lands; do not close W4 from this negative result"
        ∷ []
    }

record W4ZAdequacyFormula : Set where
  field
    chi2Formula :
      String

    alphaStarFormula :
      String

    measurementSymbol :
      String

    dirtyShapeSymbol :
      String

    luminositySymbol :
      String

    sigmaSymbol :
      String

canonicalW4ZAdequacyFormula :
  W4ZAdequacyFormula
canonicalW4ZAdequacyFormula =
  record
    { chi2Formula =
        "chi2(alpha) = sum_i ((m_i - alpha d_i ell_i)^2 / sigma_i^2)"
    ; alphaStarFormula =
        "alpha* = sum_i (m_i d_i ell_i / sigma_i^2) / sum_i ((d_i ell_i)^2 / sigma_i^2)"
    ; measurementSymbol =
        "m_i = measured Z-peak bin value"
    ; dirtyShapeSymbol =
        "d_i = dirty Dashi Z-peak shape prediction"
    ; luminositySymbol =
        "ell_i = accepted Drell-Yan luminosity convention value for the bin"
    ; sigmaSymbol =
        "sigma_i = accepted per-bin uncertainty for the adequacy calculation"
    }

record W4ZAdequacyRunnerTemplate : Set where
  field
    runnerPath :
      String

    requiredFlags :
      List String

    requiredAuthoritySurface :
      String

    requiredInputVectors :
      List String

    outputArtifactSchema :
      String

    failClosedBoundary :
      List String

canonicalW4ZAdequacyRunnerTemplate :
  W4ZAdequacyRunnerTemplate
canonicalW4ZAdequacyRunnerTemplate =
  record
    { runnerPath =
        "scripts/run_w4_z_peak_adequacy.py"
    ; requiredFlags =
        "--accepted-dy-authority"
        ∷ "--measurement-csv"
        ∷ "--measurement-column"
        ∷ "--prediction-csv"
        ∷ "--prediction-column"
        ∷ "--luminosity-csv"
        ∷ "--luminosity-column"
        ∷ "--sigma-csv"
        ∷ "--sigma-column"
        ∷ "--output"
        ∷ []
    ; requiredAuthoritySurface =
        "AcceptedDYLuminosityConventionAuthority JSON receipt with status accepted or replacement"
    ; requiredInputVectors =
        "real m_i measurement vector"
        ∷ "real d_i dirty Z-peak shape prediction vector"
        ∷ "accepted ell_i Drell-Yan luminosity vector"
        ∷ "real sigma_i per-bin uncertainty vector"
        ∷ []
    ; outputArtifactSchema =
        "dashi-w4-z-peak-adequacy-v1"
    ; failClosedBoundary =
        "missing accepted DY authority exits before calculation"
        ∷ "missing or unparsable input vectors exit before artifact emission"
        ∷ "computed artifact status is computed-not-promoted"
        ∷ "runner does not decide W4 promotion"
        ∷ []
    }

canonicalAcceptedDYLuminosityConventionAuthorityPolicyHookRequest :
  AcceptedDYLuminosityConventionAuthorityPolicyHookRequest
canonicalAcceptedDYLuminosityConventionAuthorityPolicyHookRequest =
  record
    { hookState =
        requestedAtCanonicalDefinitionSite
    ; disposition =
        failClosedNoConstructorNoProvider
    ; canonicalDefinitionSite =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt"
    ; exactAuthorityName =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority"
    ; exactReceiptConsumerName =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.W4ZAdequacyReceipt"
    ; firstMissingBeforeHookRequest =
        w4ZAdequacyFirstMissingBeforeAuthorityHook
    ; firstMissingAfterHookRequest =
        w4ZAdequacyFirstMissingAfterAuthorityHook
    ; firstMissingUnchanged =
        w4ZAdequacyAuthorityHookFirstMissingUnchanged
    ; requiredHookSignature =
        "policyHook : ProviderAuthorityPacket -> AcceptedDYLuminosityConventionAuthority"
        ∷ "zAdequacyConsumer : AcceptedDYLuminosityConventionAuthority -> W4 accepted m_i/d_i/ell_i/sigma_i inputs -> W4ZAdequacyReceipt"
        ∷ "Both outputs must use the canonical W4ZAdequacyReceipt module types"
        ∷ []
    ; requiredProviderPacketFields =
        "provider identity, authority scope, trace id, and response date"
        ∷ "accepted or replacement decision for the DY luminosity convention"
        ∷ "PDF set/version, member, grid checksum, scale, rapidity, mass-bin, flavour, and integration convention"
        ∷ "accepted per-bin ell_i luminosity vector with normalization and conversion law"
        ∷ "source citation, immutable artifact references, and no-manual-overfit attestation"
        ∷ []
    ; acceptedOutputContract =
        "The hook must return an inhabitant of the exact constructorless AcceptedDYLuminosityConventionAuthority type"
        ∷ "A W4ZAdequacyReceipt may be consumed only after accepted authority and real m_i/d_i/ell_i/sigma_i inputs exist"
        ∷ "This request surface does not itself authorize W4 promotion"
        ∷ []
    ; tokenProducingHookAuthorizedHere =
        false
    ; tokenProducingHookAuthorizedHereIsFalse =
        refl
    ; acceptedAuthorityConstructedHere =
        false
    ; acceptedAuthorityConstructedHereIsFalse =
        refl
    ; noAcceptedAuthorityHere =
        acceptedDYLuminosityConventionAuthorityMissing
    ; failClosedBoundary =
        "AcceptedDYLuminosityConventionAuthority is intentionally constructorless at the canonical definition site"
        ∷ "No external provider answer or governance-authorized token-producing hook is present in this module"
        ∷ "The first missing remains missingAcceptedDYLuminosityConventionAuthority before and after this request"
        ∷ []
    }

canonicalW4AuthorityClosureRouteAudit :
  W4AuthorityClosureRouteAudit
canonicalW4AuthorityClosureRouteAudit =
  record
    { auditedDefinitionSite =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority"
    ; acceptedRoute =
        providerOrGovernanceExactHookRoute
    ; rejectedRoutes =
        publicSourceSelfIssuedRoute
        ∷ postulateToRecordRewriteRoute
        ∷ localShadowRecordRoute
        ∷ []
    ; publicSourceEvidencePreserved =
        true
    ; publicSourceEvidencePreservedIsTrue =
        refl
    ; exactAcceptedAuthorityAvailableHere =
        false
    ; exactAcceptedAuthorityAvailableHereIsFalse =
        refl
    ; postulateToRecordRewriteAuthorizedHere =
        false
    ; postulateToRecordRewriteAuthorizedHereIsFalse =
        refl
    ; noAcceptedAuthorityHere =
        acceptedDYLuminosityConventionAuthorityMissing
    ; auditBoundary =
        "Public CMS/HEPData evidence is preserved as evidence, not converted into authority"
        ∷ "A local postulate-to-record rewrite would change the governance type and is not authorized in this lane"
        ∷ "A local shadow record cannot inhabit the canonical constructorless authority type"
        ∷ "The only accepted closure route is an exact provider/governance hook returning this module's AcceptedDYLuminosityConventionAuthority, or an owner-approved constructor in this canonical module"
        ∷ []
    }

record W4ZAdequacyReceipt : Setω where
  field
    acceptedAuthority :
      AcceptedDYLuminosityConventionAuthority

    formula :
      W4ZAdequacyFormula

    runnerArtifactDigest :
      String

    alphaStar :
      Float

    chi2 :
      Float

    dof :
      String

    chi2PerDof :
      Float

    adequacyThreshold :
      String

    adequacyDecision :
      Bool

    typedReviewStatus :
      String

    noW4Promotion :
      ⊤

record W4ZAdequacyReceiptTemplate : Setω where
  field
    status :
      W4ZAdequacyStatus

    firstMissing :
      W4ZAdequacyFirstMissing

    formula :
      W4ZAdequacyFormula

    formulaIsCanonical :
      formula
      ≡
      canonicalW4ZAdequacyFormula

    runnerTemplate :
      W4ZAdequacyRunnerTemplate

    runnerTemplateIsCanonical :
      runnerTemplate
      ≡
      canonicalW4ZAdequacyRunnerTemplate

    dirtyZPeakBaselineChi2PerDof :
      String

    dirtyZPeakBaselineResult :
      W4ZAdequacyResult

    dirtyZPeakBaselineResultIsCanonical :
      dirtyZPeakBaselineResult
      ≡
      canonicalDirtyZPeakObstructedResult

    requiredAuthority :
      String

    requiredLuminosityVector :
      String

    requiredRealDataInputs :
      List String

    receiptPromotionBoundary :
      List String

    noAcceptedAuthorityHere :
      AcceptedDYLuminosityConventionAuthority →
      ⊥

    noW4ZAdequacyReceiptHere :
      W4ZAdequacyReceipt →
      ⊥

    promotesW4 :
      Bool

    noW4Promotion :
      ⊤

canonicalW4ZAdequacyReceiptTemplate :
  W4ZAdequacyReceiptTemplate
canonicalW4ZAdequacyReceiptTemplate =
  record
    { status =
        blockedAwaitingAcceptedDYLuminosityConventionAuthority
    ; firstMissing =
        missingAcceptedDYLuminosityConventionAuthority
    ; formula =
        canonicalW4ZAdequacyFormula
    ; formulaIsCanonical =
        refl
    ; runnerTemplate =
        canonicalW4ZAdequacyRunnerTemplate
    ; runnerTemplateIsCanonical =
        refl
    ; dirtyZPeakBaselineChi2PerDof =
        "298.8462841768543"
    ; dirtyZPeakBaselineResult =
        canonicalDirtyZPeakObstructedResult
    ; dirtyZPeakBaselineResultIsCanonical =
        refl
    ; requiredAuthority =
        "AcceptedDYLuminosityConventionAuthority must accept the DY luminosity convention, bin integration, scale, flavour sum, PDF member/error treatment, and provenance"
    ; requiredLuminosityVector =
        "accepted per-bin ell_i luminosity vector aligned to the Z-peak m_i/d_i/sigma_i bins"
    ; requiredRealDataInputs =
        "measurement CSV column for m_i"
        ∷ "prediction CSV column for d_i"
        ∷ "luminosity CSV column for ell_i"
        ∷ "uncertainty CSV column for sigma_i"
        ∷ []
    ; receiptPromotionBoundary =
        "This template prepares the gated W4 adequacy path only"
        ∷ "It does not accept the W4/W5 shared luminosity convention"
        ∷ "It does not claim adequacy for the dirty Z-peak baseline"
        ∷ "It does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "It does not promote W4"
        ∷ []
    ; noAcceptedAuthorityHere =
        acceptedDYLuminosityConventionAuthorityMissing
    ; noW4ZAdequacyReceiptHere =
        λ receipt →
          acceptedDYLuminosityConventionAuthorityMissing
            (W4ZAdequacyReceipt.acceptedAuthority receipt)
    ; promotesW4 =
        false
    ; noW4Promotion =
        tt
    }

canonicalW4ZAdequacyTemplateNoPromotion :
  W4ZAdequacyReceiptTemplate.promotesW4
    canonicalW4ZAdequacyReceiptTemplate
    ≡ false
canonicalW4ZAdequacyTemplateNoPromotion =
  refl
