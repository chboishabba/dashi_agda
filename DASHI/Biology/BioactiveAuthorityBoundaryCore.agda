module DASHI.Biology.BioactiveAuthorityBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- Bioactive authority-boundary core.
--
-- This module is the biology/pharmacology specialization that keeps the
-- local surface fail-closed while the generic authority-boundary spine lands
-- in DASHI.Promotion.AuthorityBoundaryCore.  It records the canonical
-- blocked-claim vocabulary and the compatibility projections that preserve
-- the existing local false/blocking surfaces.

data BioactiveBlockedClaim : Set where
  clinicalAuthorityBlockedClaim :
    BioactiveBlockedClaim

  doseResponseAuthorityBlockedClaim :
    BioactiveBlockedClaim

  prescribingAuthorityBlockedClaim :
    BioactiveBlockedClaim

  diseaseAuthorityBlockedClaim :
    BioactiveBlockedClaim

  behaviorAuthorityBlockedClaim :
    BioactiveBlockedClaim

  biomarkerAuthorityBlockedClaim :
    BioactiveBlockedClaim

  receptorActionIdentityBlockedClaim :
    BioactiveBlockedClaim

  shapeEffectIdentityBlockedClaim :
    BioactiveBlockedClaim

canonicalBioactiveBlockedClaims : List BioactiveBlockedClaim
canonicalBioactiveBlockedClaims =
  clinicalAuthorityBlockedClaim
  ∷ doseResponseAuthorityBlockedClaim
  ∷ prescribingAuthorityBlockedClaim
  ∷ diseaseAuthorityBlockedClaim
  ∷ behaviorAuthorityBlockedClaim
  ∷ biomarkerAuthorityBlockedClaim
  ∷ receptorActionIdentityBlockedClaim
  ∷ shapeEffectIdentityBlockedClaim
  ∷ []

blockedClaimFlag : BioactiveBlockedClaim -> Bool
blockedClaimFlag _ = false

blockedClaimFlagIsFalse :
  (claim : BioactiveBlockedClaim) ->
  blockedClaimFlag claim ≡ false
blockedClaimFlagIsFalse _ = refl

record BioactiveAuthorityBoundaryCore : Set₁ where
  constructor mkBioactiveAuthorityBoundaryCore
  field
    blockedClaims :
      List BioactiveBlockedClaim

    blockedClaimsAreCanonical :
      blockedClaims ≡ canonicalBioactiveBlockedClaims

    genericAuthorityBoundaryReceipt :
      AuthorityBoundary.AuthorityBoundaryReceipt

    genericAuthorityBoundaryReceiptIsCanonical :
      genericAuthorityBoundaryReceipt ≡
      AuthorityBoundary.canonicalBioactiveAuthorityBoundaryReceipt

    genericBoundaryPromotedIsFalse :
      AuthorityBoundary.receiptBoundaryPromoted
        genericAuthorityBoundaryReceipt
      ≡
      false

    clinicalAuthorityClaimFlag :
      Bool

    clinicalAuthorityClaimFlagIsFalse :
      clinicalAuthorityClaimFlag ≡ false

    doseResponseAuthorityClaimFlag :
      Bool

    doseResponseAuthorityClaimFlagIsFalse :
      doseResponseAuthorityClaimFlag ≡ false

    prescribingAuthorityClaimFlag :
      Bool

    prescribingAuthorityClaimFlagIsFalse :
      prescribingAuthorityClaimFlag ≡ false

    diseaseAuthorityClaimFlag :
      Bool

    diseaseAuthorityClaimFlagIsFalse :
      diseaseAuthorityClaimFlag ≡ false

    behaviorAuthorityClaimFlag :
      Bool

    behaviorAuthorityClaimFlagIsFalse :
      behaviorAuthorityClaimFlag ≡ false

    biomarkerAuthorityClaimFlag :
      Bool

    biomarkerAuthorityClaimFlagIsFalse :
      biomarkerAuthorityClaimFlag ≡ false

    receptorActionIdentityAuthorityClaimFlag :
      Bool

    receptorActionIdentityAuthorityClaimFlagIsFalse :
      receptorActionIdentityAuthorityClaimFlag ≡ false

    shapeEffectIdentityAuthorityClaimFlag :
      Bool

    shapeEffectIdentityAuthorityClaimFlagIsFalse :
      shapeEffectIdentityAuthorityClaimFlag ≡ false

open BioactiveAuthorityBoundaryCore public

canonicalBioactiveAuthorityBoundaryCore :
  BioactiveAuthorityBoundaryCore
canonicalBioactiveAuthorityBoundaryCore =
  mkBioactiveAuthorityBoundaryCore
    canonicalBioactiveBlockedClaims
    refl
    AuthorityBoundary.canonicalBioactiveAuthorityBoundaryReceipt
    refl
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
    false
    refl
    false
    refl
    false
    refl

canonicalClinicalAuthorityClaimFlagIsFalse :
  clinicalAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalClinicalAuthorityClaimFlagIsFalse =
  clinicalAuthorityClaimFlagIsFalse canonicalBioactiveAuthorityBoundaryCore

canonicalDoseResponseAuthorityClaimFlagIsFalse :
  doseResponseAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalDoseResponseAuthorityClaimFlagIsFalse =
  doseResponseAuthorityClaimFlagIsFalse canonicalBioactiveAuthorityBoundaryCore

canonicalPrescribingAuthorityClaimFlagIsFalse :
  prescribingAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalPrescribingAuthorityClaimFlagIsFalse =
  prescribingAuthorityClaimFlagIsFalse canonicalBioactiveAuthorityBoundaryCore

canonicalDiseaseAuthorityClaimFlagIsFalse :
  diseaseAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalDiseaseAuthorityClaimFlagIsFalse =
  diseaseAuthorityClaimFlagIsFalse canonicalBioactiveAuthorityBoundaryCore

canonicalBehaviorAuthorityClaimFlagIsFalse :
  behaviorAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalBehaviorAuthorityClaimFlagIsFalse =
  behaviorAuthorityClaimFlagIsFalse canonicalBioactiveAuthorityBoundaryCore

canonicalBiomarkerAuthorityClaimFlagIsFalse :
  biomarkerAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalBiomarkerAuthorityClaimFlagIsFalse =
  biomarkerAuthorityClaimFlagIsFalse canonicalBioactiveAuthorityBoundaryCore

canonicalReceptorActionIdentityAuthorityClaimFlagIsFalse :
  receptorActionIdentityAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalReceptorActionIdentityAuthorityClaimFlagIsFalse =
  receptorActionIdentityAuthorityClaimFlagIsFalse
    canonicalBioactiveAuthorityBoundaryCore

canonicalShapeEffectIdentityAuthorityClaimFlagIsFalse :
  shapeEffectIdentityAuthorityClaimFlag canonicalBioactiveAuthorityBoundaryCore ≡ false
canonicalShapeEffectIdentityAuthorityClaimFlagIsFalse =
  shapeEffectIdentityAuthorityClaimFlagIsFalse
    canonicalBioactiveAuthorityBoundaryCore
