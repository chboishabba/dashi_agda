module DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_<_)

import DASHI.Physics.Closure.W4ResponseMatrixAcceptanceCandidateReceipt as Candidate
import DASHI.Physics.Closure.W4ZAdequacyReceipt as W4Z
import DASHI.Physics.Closure.ExternalAuthorityImportCore as AuthorityCore

------------------------------------------------------------------------
-- W4 external authority token surface.
--
-- This module is request-only.  It gives the provider the exact fields
-- needed for W4 Z-window adequacy and downstream physical calibration, while
-- keeping the local authority token constructorless.  No W4 promotion,
-- adequacy receipt, or physical calibration receipt is fabricated here.  The
-- public Table 2/3 context and response-matrix diagnostics do not provide a
-- central efficiency/acceptance model.  The older 9566 > 9000 diagonal
-- arithmetic is retained only as a rejected diagnostic and does not construct
-- W4ZAdequacy.

data W4ExternalAuthorityToken : Set where

w4ExternalAuthorityTokenUnavailable :
  W4ExternalAuthorityToken →
  ⊥
w4ExternalAuthorityTokenUnavailable ()

data W4ExternalAuthorityRequestStatus : Set where
  blockedAwaitingExternalAuthorityToken :
    W4ExternalAuthorityRequestStatus
  publicSourceSelfPopulationAttemptFailClosed :
    W4ExternalAuthorityRequestStatus

data W4ExternalAuthorityMissingField : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    W4ExternalAuthorityMissingField
  missingW4ZAdequacyConsumer :
    W4ExternalAuthorityMissingField
  missingAcceptedPerBinLuminosityVector :
    W4ExternalAuthorityMissingField
  missingInternalDiagonalConvention :
    W4ExternalAuthorityMissingField
  missingLeptonChannelCombineConvention :
    W4ExternalAuthorityMissingField
  missingZAndBelowZAnchorBinding :
    W4ExternalAuthorityMissingField
  missingProviderIdentityAndDate :
    W4ExternalAuthorityMissingField
  missingStrictInequalityOrAdequacyThresholdPrimitive :
    W4ExternalAuthorityMissingField

data W4PublicSourceAuthorityBasis : Set where
  publicCMSPaperAndHEPData :
    W4PublicSourceAuthorityBasis

data W4AuthoritySelfPopulationBlocker : Set where
  missingW4ExternalAuthorityTokenConstructor :
    W4AuthoritySelfPopulationBlocker
  missingAcceptedDYLuminosityConventionAuthorityConstructor :
    W4AuthoritySelfPopulationBlocker
  missingTokenProducingPolicyHookForPublicCMSPaperAndHEPData :
    W4AuthoritySelfPopulationBlocker
  missingW4ZAdequacyReceiptConsumer :
    W4AuthoritySelfPopulationBlocker

canonicalW4AuthoritySelfPopulationBlockers :
  List W4AuthoritySelfPopulationBlocker
canonicalW4AuthoritySelfPopulationBlockers =
  missingW4ExternalAuthorityTokenConstructor
  ∷ missingAcceptedDYLuminosityConventionAuthorityConstructor
  ∷ missingTokenProducingPolicyHookForPublicCMSPaperAndHEPData
  ∷ missingW4ZAdequacyReceiptConsumer
  ∷ []

data W4AuthorityPolicyHookState : Set where
  requestedButNoCanonicalTokenProducingHook :
    W4AuthorityPolicyHookState
  governancePolicyExplicitlyNonW4TokenProducing :
    W4AuthorityPolicyHookState

data W4AuthorityPolicyHookDisposition : Set where
  failClosedRequestOnly :
    W4AuthorityPolicyHookDisposition

w4AuthorityFirstMissingBeforePolicyHookRequest :
  W4ExternalAuthorityMissingField
w4AuthorityFirstMissingBeforePolicyHookRequest =
  missingAcceptedDYLuminosityConventionAuthority

w4AuthorityFirstMissingAfterPolicyHookRequest :
  W4ExternalAuthorityMissingField
w4AuthorityFirstMissingAfterPolicyHookRequest =
  missingAcceptedDYLuminosityConventionAuthority

w4AuthorityPolicyHookRequestFirstMissingUnchanged :
  w4AuthorityFirstMissingAfterPolicyHookRequest
  ≡
  w4AuthorityFirstMissingBeforePolicyHookRequest
w4AuthorityPolicyHookRequestFirstMissingUnchanged =
  refl

data W4DiagonalConvention : Set where
  internalPressureDiagonal :
    W4DiagonalConvention

data W4ChannelCombineConvention : Set where
  providerMustStateElectronMuonCombination :
    W4ChannelCombineConvention

data W4AnchorRole : Set where
  zWindowAnchor :
    W4AnchorRole
  belowZWindowAnchor :
    W4AnchorRole

record W4ExternalAuthorityProviderRequest : Setω where
  field
    externalAuthorityImportCore :
      AuthorityCore.ExternalAuthorityImportReceipt

    externalAuthorityImportCoreIsCanonical :
      externalAuthorityImportCore
      ≡
      AuthorityCore.w4TokenExternalAuthorityImportReceipt

    externalAuthorityImportCoreTokenFalse :
      AuthorityCore.tokenPresent externalAuthorityImportCore ≡ false

    requestStatus :
      W4ExternalAuthorityRequestStatus

    exactAuthorityTokenName :
      String

    exactDYLuminosityAuthorityName :
      String

    exactZAdequacyReceiptName :
      String

    exactPhysicalCalibrationReceiptName :
      String

    missingProviderFields :
      List W4ExternalAuthorityMissingField

    requestedLuminosityFields :
      List String

    diagonalConvention :
      W4DiagonalConvention

    diagonalConventionFields :
      List String

    channelCombineConvention :
      W4ChannelCombineConvention

    channelCombineFields :
      List String

    anchorRoles :
      List W4AnchorRole

    zAndBelowZAnchorFields :
      List String

    providerAndDateFields :
      List String

    acceptedDecisionFields :
      List String

    strictInequalityBlocker :
      List String

    internalStrictInequalityDischarged :
      Bool

    internalStrictInequalityDischargedIsFalse :
      internalStrictInequalityDischarged ≡ false

    internalStrictInequalityWitness :
      9000 < 9566

    nonPromotionBoundary :
      List String

    promotesW4 :
      Bool

    promotesW4IsFalse :
      promotesW4 ≡ false

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere ≡ false

    adequacyReceiptConstructedHere :
      Bool

    adequacyReceiptConstructedHereIsFalse :
      adequacyReceiptConstructedHere ≡ false

    physicalCalibrationReceiptConstructedHere :
      Bool

    physicalCalibrationReceiptConstructedHereIsFalse :
      physicalCalibrationReceiptConstructedHere ≡ false

    noLocalW4AuthorityToken :
      W4ExternalAuthorityToken →
      ⊥

    noLocalAcceptedDYLuminosityAuthority :
      W4Z.AcceptedDYLuminosityConventionAuthority →
      ⊥

    noW4PromotionWitness :
      ⊤

record W4PublicSourceAuthoritySelfPopulationAttempt : Setω where
  field
    requestStatus :
      W4ExternalAuthorityRequestStatus

    authorityBasis :
      W4PublicSourceAuthorityBasis

    authorityBasisText :
      String

    externalClaim :
      Bool

    externalClaimIsFalse :
      externalClaim ≡ false

    publicSourceEvidence :
      List String

    requestedResultTypes :
      List String

    exactBlockers :
      List W4AuthoritySelfPopulationBlocker

    exactBlockersAreCanonical :
      exactBlockers ≡ canonicalW4AuthoritySelfPopulationBlockers

    governanceSelfIssuancePolicyPath :
      String

    governanceSelfIssuanceW4Ruling :
      String

    canSelfPopulateToken :
      Bool

    canSelfPopulateTokenIsFalse :
      canSelfPopulateToken ≡ false

    canSelfPopulateAcceptedDYLuminosityAuthority :
      Bool

    canSelfPopulateAcceptedDYLuminosityAuthorityIsFalse :
      canSelfPopulateAcceptedDYLuminosityAuthority ≡ false

    internalStrictInequalityDischarged :
      Bool

    internalStrictInequalityDischargedIsFalse :
      internalStrictInequalityDischarged ≡ false

    internalStrictInequalityWitness :
      9000 < 9566

    noLocalW4AuthorityToken :
      W4ExternalAuthorityToken →
      ⊥

    noLocalAcceptedDYLuminosityAuthority :
      W4Z.AcceptedDYLuminosityConventionAuthority →
      ⊥

    noW4ZAdequacyReceiptFromPublicSourceAttempt :
      W4Z.W4ZAdequacyReceipt →
      ⊥

    failClosedBoundary :
      List String

record W4LuminosityZAdequacyPolicyHookRequest : Setω where
  field
    hookState :
      W4AuthorityPolicyHookState

    disposition :
      W4AuthorityPolicyHookDisposition

    authorityBasis :
      W4PublicSourceAuthorityBasis

    selfPopulationAttempt :
      W4PublicSourceAuthoritySelfPopulationAttempt

    canonicalAuthorityOwnerModule :
      String

    exactAcceptedDYLuminosityAuthorityName :
      String

    exactW4ZAdequacyReceiptName :
      String

    governanceSelfIssuancePolicyPath :
      String

    governanceW4NoOverreachRuling :
      String

    exactHookSignatureRequired :
      List String

    hookInputFields :
      List String

    hookOutputFields :
      List String

    firstMissingBeforeHookRequest :
      W4ExternalAuthorityMissingField

    firstMissingAfterHookRequest :
      W4ExternalAuthorityMissingField

    firstMissingUnchanged :
      firstMissingAfterHookRequest
      ≡
      firstMissingBeforeHookRequest

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow ≡ false

    acceptedDYLuminosityAuthorityConstructedHere :
      Bool

    acceptedDYLuminosityAuthorityConstructedHereIsFalse :
      acceptedDYLuminosityAuthorityConstructedHere ≡ false

    w4ZAdequacyReceiptConstructedHere :
      Bool

    w4ZAdequacyReceiptConstructedHereIsFalse :
      w4ZAdequacyReceiptConstructedHere ≡ false

    noLocalAcceptedDYLuminosityAuthority :
      W4Z.AcceptedDYLuminosityConventionAuthority →
      ⊥

    noW4ZAdequacyReceiptFromHookRequest :
      W4Z.W4ZAdequacyReceipt →
      ⊥

    failClosedBoundary :
      List String

canonicalW4ExternalAuthorityProviderRequest :
  W4ExternalAuthorityProviderRequest
canonicalW4ExternalAuthorityProviderRequest =
  record
    { externalAuthorityImportCore =
        AuthorityCore.w4TokenExternalAuthorityImportReceipt
    ; externalAuthorityImportCoreIsCanonical =
        refl
    ; externalAuthorityImportCoreTokenFalse =
        refl
    ; requestStatus =
        publicSourceSelfPopulationAttemptFailClosed
    ; exactAuthorityTokenName =
        "DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface.W4ExternalAuthorityToken"
    ; exactDYLuminosityAuthorityName =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority"
    ; exactZAdequacyReceiptName =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.W4ZAdequacyReceipt"
    ; exactPhysicalCalibrationReceiptName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"
    ; missingProviderFields =
        missingAcceptedDYLuminosityConventionAuthority
        ∷ missingW4ZAdequacyConsumer
        ∷ missingAcceptedPerBinLuminosityVector
        ∷ missingInternalDiagonalConvention
        ∷ missingLeptonChannelCombineConvention
        ∷ missingZAndBelowZAnchorBinding
        ∷ missingProviderIdentityAndDate
        ∷ []
    ; requestedLuminosityFields =
        "source integrated luminosity binding: L_int = 36.3 fb^-1 for CMS-SMP-20-003 / ins2079374"
        ∷ "do not substitute the full Run-2 137 fb^-1 luminosity for this 2016 CMS-SMP-20-003 package"
        ∷ "W4 per-phi-star-bin luminosity vector ell_i for the 76-106 GeV Z window"
        ∷ "luminosity definition: PDF set/version, LHAPDF id or equivalent, factorization scale, rapidity/fiducial convention, and bin integration"
        ∷ "normalization preservation law from provider luminosities to the W4 adequacy runner"
        ∷ "covariance/systematic propagation for the accepted per-bin luminosity convention"
        ∷ []
    ; diagonalConvention =
        internalPressureDiagonal
    ; diagonalConventionFields =
        "Do not use CMS-SMP-20-003 Table 2/3 or response-matrix diagonals as a central efficiency/acceptance model"
        ∷ "State whether any provider-supplied diagonal is covariance diagonal, inverse-covariance diagonal, full covariance contraction, or an independent acceptance model"
        ∷ "Bind the conversion from provider diagonal entries to sigma_i in W4ZAdequacyReceipt.canonicalW4ZAdequacyFormula"
        ∷ []
    ; channelCombineConvention =
        providerMustStateElectronMuonCombination
    ; channelCombineFields =
        "State electron-channel, muon-channel, or combined-channel treatment"
        ∷ "If combined, provide the exact combination law and covariance propagation"
        ∷ "If single-channel, state why the channel is authoritative for W4"
        ∷ []
    ; anchorRoles =
        zWindowAnchor
        ∷ belowZWindowAnchor
        ∷ []
    ; zAndBelowZAnchorFields =
        "Z anchor: CMS-SMP-20-003 76-106 GeV DSIG/DPHISTAR measurement table and covariance binding"
        ∷ "Below-Z anchor: CMS-SMP-20-003 50-76 GeV ratio/cross-section table binding for convention continuity checks"
        ∷ "Provide DOI/public URL, table ids, checksums, and immutable artifact references for both anchors"
        ∷ []
    ; providerAndDateFields =
        "provider identity"
        ∷ "provider role and authority scope"
        ∷ "contact or trace id"
        ∷ "response date"
        ∷ "source citation date or artifact retrieval date"
        ∷ []
    ; acceptedDecisionFields =
        "decision must be accepted, replacement, rejected, or insufficient"
        ∷ "accepted/replacement responses must bind every requested field above"
        ∷ "rejected/insufficient responses must name the exact failed rule or missing field"
        ∷ []
    ; strictInequalityBlocker =
        "The former 9566 > 9000 diagonal-response arithmetic is rejected as W4 adequacy evidence because the source lacks a central efficiency/acceptance model"
        ∷ "Table 2/3 and response matrices do not construct AcceptedDYLuminosityConventionAuthority"
        ∷ "W4 adequacy remains blocked on the accepted DY luminosity authority, accepted per-bin luminosity vector, source efficiency/acceptance model or accepted conversion law, and W4ZAdequacy consumer"
        ∷ []
    ; internalStrictInequalityDischarged =
        false
    ; internalStrictInequalityDischargedIsFalse =
        refl
    ; internalStrictInequalityWitness =
        Candidate.scaledDecimalStrictGreaterThan9566over9000
    ; nonPromotionBoundary =
        "This module is a constructorless provider request surface"
        ∷ "It does not construct W4ExternalAuthorityToken"
        ∷ "It does not construct AcceptedDYLuminosityConventionAuthority"
        ∷ "It does not construct W4ZAdequacyReceipt"
        ∷ "It does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not promote W4"
        ∷ []
    ; promotesW4 =
        false
    ; promotesW4IsFalse =
        refl
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; adequacyReceiptConstructedHere =
        false
    ; adequacyReceiptConstructedHereIsFalse =
        refl
    ; physicalCalibrationReceiptConstructedHere =
        false
    ; physicalCalibrationReceiptConstructedHereIsFalse =
        refl
    ; noLocalW4AuthorityToken =
        w4ExternalAuthorityTokenUnavailable
    ; noLocalAcceptedDYLuminosityAuthority =
        W4Z.acceptedDYLuminosityConventionAuthorityMissing
    ; noW4PromotionWitness =
        tt
    }

canonicalW4PublicSourceAuthoritySelfPopulationAttempt :
  W4PublicSourceAuthoritySelfPopulationAttempt
canonicalW4PublicSourceAuthoritySelfPopulationAttempt =
  record
    { requestStatus =
        publicSourceSelfPopulationAttemptFailClosed
    ; authorityBasis =
        publicCMSPaperAndHEPData
    ; authorityBasisText =
        "authorityBasis = public paper/data: CMS-SMP-20-003 public paper plus HEPData ins2079374 tables and local checksum-bound diagnostics"
    ; externalClaim =
        false
    ; externalClaimIsFalse =
        refl
    ; publicSourceEvidence =
        "CMS-SMP-20-003 public result / HEPData ins2079374"
        ∷ "scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
        ∷ "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"
        ∷ "scripts/data/hepdata/ins2079374_response_phistar_t68_t77.sha256"
        ∷ "scripts/data/outputs/w4w5_hepdata_response_matrix_diagnostic.json"
        ∷ []
    ; requestedResultTypes =
        "DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface.W4ExternalAuthorityToken"
        ∷ "DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority"
        ∷ "DASHI.Physics.Closure.W4ZAdequacyReceipt.W4ZAdequacyReceipt"
        ∷ []
    ; exactBlockers =
        canonicalW4AuthoritySelfPopulationBlockers
    ; exactBlockersAreCanonical =
        refl
    ; governanceSelfIssuancePolicyPath =
        "Docs/DASHIGovernanceSelfIssuancePolicy.md"
    ; governanceSelfIssuanceW4Ruling =
        "No-overreach clause excludes W4/W5 Drell-Yan convention or physical-unit authority from W2/W3 public-source self-issuance"
    ; canSelfPopulateToken =
        false
    ; canSelfPopulateTokenIsFalse =
        refl
    ; canSelfPopulateAcceptedDYLuminosityAuthority =
        false
    ; canSelfPopulateAcceptedDYLuminosityAuthorityIsFalse =
        refl
    ; internalStrictInequalityDischarged =
        false
    ; internalStrictInequalityDischargedIsFalse =
        refl
    ; internalStrictInequalityWitness =
        Candidate.scaledDecimalStrictGreaterThan9566over9000
    ; noLocalW4AuthorityToken =
        w4ExternalAuthorityTokenUnavailable
    ; noLocalAcceptedDYLuminosityAuthority =
        W4Z.acceptedDYLuminosityConventionAuthorityMissing
    ; noW4ZAdequacyReceiptFromPublicSourceAttempt =
        λ receipt →
          W4Z.acceptedDYLuminosityConventionAuthorityMissing
            (W4Z.W4ZAdequacyReceipt.acceptedAuthority receipt)
    ; failClosedBoundary =
        "Public CMS paper/data can be recorded as authorityBasis with externalClaim=false"
        ∷ "No CMS response or external countersignature is claimed"
        ∷ "Self-population is impossible here because W4ExternalAuthorityToken has no constructor"
        ∷ "Self-population is impossible here because W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority has no constructor"
        ∷ "No token-producing policy hook from public CMS paper/HEPData evidence to those exact result types exists"
        ∷ "The former 9566 > 9000 diagonal arithmetic is rejected as source-inadequate; W4ZAdequacy and accepted DY luminosity authority remain uninhabited"
        ∷ []
    }

canonicalW4LuminosityZAdequacyPolicyHookRequest :
  W4LuminosityZAdequacyPolicyHookRequest
canonicalW4LuminosityZAdequacyPolicyHookRequest =
  record
    { hookState =
        governancePolicyExplicitlyNonW4TokenProducing
    ; disposition =
        failClosedRequestOnly
    ; authorityBasis =
        publicCMSPaperAndHEPData
    ; selfPopulationAttempt =
        canonicalW4PublicSourceAuthoritySelfPopulationAttempt
    ; canonicalAuthorityOwnerModule =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt"
    ; exactAcceptedDYLuminosityAuthorityName =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority"
    ; exactW4ZAdequacyReceiptName =
        "DASHI.Physics.Closure.W4ZAdequacyReceipt.W4ZAdequacyReceipt"
    ; governanceSelfIssuancePolicyPath =
        "Docs/DASHIGovernanceSelfIssuancePolicy.md"
    ; governanceW4NoOverreachRuling =
        "The current self-issuance policy is W2/W3-scoped and explicitly does not promote W4/W5 Drell-Yan convention or physical-unit authority"
    ; exactHookSignatureRequired =
        "policyHook : W4PublicSourceAuthorityBasis -> ProviderAuthorityPacket -> AcceptedDYLuminosityConventionAuthority"
        ∷ "zAdequacyConsumer : AcceptedDYLuminosityConventionAuthority -> W4 accepted m_i/d_i/ell_i/sigma_i inputs -> W4ZAdequacyReceipt"
        ∷ "Both result types must be the canonical W4ZAdequacyReceipt module types, not local shadow records"
        ∷ []
    ; hookInputFields =
        "authorityBasis = publicCMSPaperAndHEPData"
        ∷ "provider identity, authority scope, trace id, and response date"
        ∷ "CMS-SMP-20-003 / HEPData table ids, DOI/public URL, checksums, and retrieval date"
        ∷ "accepted PDF/luminosity convention, per-bin ell_i vector, normalization law, conversion law, and systematic budget"
        ∷ "accepted W4 m_i/d_i/ell_i/sigma_i binding, threshold, and typed review rule"
        ∷ []
    ; hookOutputFields =
        "AcceptedDYLuminosityConventionAuthority"
        ∷ "W4ZAdequacyReceipt with acceptedAuthority field inhabited by that authority"
        ∷ "non-promotion boundary for Candidate256 physical calibration and downstream matter/stress-energy"
        ∷ []
    ; firstMissingBeforeHookRequest =
        w4AuthorityFirstMissingBeforePolicyHookRequest
    ; firstMissingAfterHookRequest =
        w4AuthorityFirstMissingAfterPolicyHookRequest
    ; firstMissingUnchanged =
        w4AuthorityPolicyHookRequestFirstMissingUnchanged
    ; tokenProducingHookAuthorizedNow =
        false
    ; tokenProducingHookAuthorizedNowIsFalse =
        refl
    ; acceptedDYLuminosityAuthorityConstructedHere =
        false
    ; acceptedDYLuminosityAuthorityConstructedHereIsFalse =
        refl
    ; w4ZAdequacyReceiptConstructedHere =
        false
    ; w4ZAdequacyReceiptConstructedHereIsFalse =
        refl
    ; noLocalAcceptedDYLuminosityAuthority =
        W4Z.acceptedDYLuminosityConventionAuthorityMissing
    ; noW4ZAdequacyReceiptFromHookRequest =
        λ receipt →
          W4Z.acceptedDYLuminosityConventionAuthorityMissing
            (W4Z.W4ZAdequacyReceipt.acceptedAuthority receipt)
    ; failClosedBoundary =
        "No canonical token-producing policy hook exists in the current W4 authority owner module"
        ∷ "The legitimate hook must return the exact constructorless AcceptedDYLuminosityConventionAuthority type or the owner must add a real constructor"
        ∷ "W4ZAdequacyReceipt remains impossible here because its acceptedAuthority field cannot be inhabited locally"
        ∷ "Recording the hook signature does not authorize public-source self-population"
        ∷ "The canonical route audit rejects public-source self-issued closure, local shadow records, and local postulate-to-record rewrites"
        ∷ []
    }

canonicalW4ExternalAuthorityDoesNotPromote :
  W4ExternalAuthorityProviderRequest.promotesW4
    canonicalW4ExternalAuthorityProviderRequest
  ≡
  false
canonicalW4ExternalAuthorityDoesNotPromote =
  refl

canonicalW4ExternalAuthorityConstructsNoToken :
  W4ExternalAuthorityProviderRequest.authorityTokenConstructedHere
    canonicalW4ExternalAuthorityProviderRequest
  ≡
  false
canonicalW4ExternalAuthorityConstructsNoToken =
  refl

canonicalW4ExternalAuthorityConstructsNoAdequacyReceipt :
  W4ExternalAuthorityProviderRequest.adequacyReceiptConstructedHere
    canonicalW4ExternalAuthorityProviderRequest
  ≡
  false
canonicalW4ExternalAuthorityConstructsNoAdequacyReceipt =
  refl
