module DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4ZAdequacyReceipt as W4Z

------------------------------------------------------------------------
-- W4 external authority token surface.
--
-- This module is request-only.  It gives the provider the exact fields
-- needed for W4 Z-window adequacy and downstream physical calibration, while
-- keeping the local authority token constructorless.  No W4 promotion,
-- adequacy receipt, physical calibration receipt, or strict inequality
-- primitive is fabricated here.

data W4ExternalAuthorityToken : Set where

w4ExternalAuthorityTokenUnavailable :
  W4ExternalAuthorityToken →
  ⊥
w4ExternalAuthorityTokenUnavailable ()

data W4ExternalAuthorityRequestStatus : Set where
  blockedAwaitingExternalAuthorityToken :
    W4ExternalAuthorityRequestStatus

data W4ExternalAuthorityMissingField : Set where
  missingAcceptedDYLuminosityConventionAuthority :
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

canonicalW4ExternalAuthorityProviderRequest :
  W4ExternalAuthorityProviderRequest
canonicalW4ExternalAuthorityProviderRequest =
  record
    { requestStatus =
        blockedAwaitingExternalAuthorityToken
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
        ∷ missingAcceptedPerBinLuminosityVector
        ∷ missingInternalDiagonalConvention
        ∷ missingLeptonChannelCombineConvention
        ∷ missingZAndBelowZAnchorBinding
        ∷ missingProviderIdentityAndDate
        ∷ missingStrictInequalityOrAdequacyThresholdPrimitive
        ∷ []
    ; requestedLuminosityFields =
        "W4 per-phi-star-bin luminosity vector ell_i for the 76-106 GeV Z window"
        ∷ "luminosity definition: PDF set/version, LHAPDF id or equivalent, factorization scale, rapidity/fiducial convention, and bin integration"
        ∷ "normalization preservation law from provider luminosities to the W4 adequacy runner"
        ∷ "covariance/systematic propagation for the accepted per-bin luminosity convention"
        ∷ []
    ; diagonalConvention =
        internalPressureDiagonal
    ; diagonalConventionFields =
        "Use the internal W4 diagonal convention already consumed by the pressure/adequacy surface"
        ∷ "State whether the provider diagonal is covariance diagonal, inverse-covariance diagonal, or full covariance contraction"
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
        "The strict inequality or adequacy-threshold primitive is not supplied by this module"
        ∷ "A provider may supply an authority-backed threshold or strict comparison rule; this surface only requests it"
        ∷ "Without that primitive, W4 adequacy remains blocked even if diagnostic vectors are present"
        ∷ []
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
