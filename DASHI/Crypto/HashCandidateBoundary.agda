module DASHI.Crypto.HashCandidateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.FingerprintProjectionCore as Fingerprint
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Hash candidate boundary.
--
-- The module consumes the fingerprint projection core and keeps the local
-- claim set fail-closed.  Digest equality is treated as candidate-only
-- information, while digest-equality -> object-equality, content-address,
-- signature-root, and adversarial-integrity authority stay blocked.

record HashCandidateBoundarySurface : Set₁ where
  constructor mkHashCandidateBoundarySurface
  field
    boundaryLabel :
      String

    boundaryOwner :
      String

    boundarySurfaceName :
      String

    boundaryCore :
      Fingerprint.FingerprintProjectionCore

    boundaryCollisionCollapseIdentityAuthorityBoundary :
      Fingerprint.CollisionCollapseIdentityAuthorityBoundary

    boundaryCollisionReceipt :
      Fingerprint.CollisionReceipt boundaryCore

    boundaryPreimageReceipt :
      Fingerprint.PreimageReceipt boundaryCore

    boundarySecondPreimageReceipt :
      Fingerprint.SecondPreimageReceipt boundaryCore

    boundaryGenericReceipt :
      GenericReceipt.GenericReceipt

    digestEqualityToObjectEqualityAuthority :
      Bool

    contentAddressAuthority :
      Bool

    signatureRootAuthority :
      Bool

    adversarialIntegrityAuthority :
      Bool

    boundaryStatement :
      String

    boundaryRemainingGap :
      String

open HashCandidateBoundarySurface public

record HashCandidateBoundaryReceipt
  (surface : HashCandidateBoundarySurface) :
  Set where
  constructor mkHashCandidateBoundaryReceipt
  field
    boundaryGenericReceiptNonPromoting :
      GenericReceipt.promotesClaim
        (boundaryGenericReceipt surface)
      ≡
      false

    boundaryDigestEqualityCandidateOnlyIsTrue :
      Fingerprint.digestEqualityCandidateOnly
        (boundaryCollisionCollapseIdentityAuthorityBoundary surface)
      ≡
      true

    boundaryCollisionIdentityAuthorityIsFalse :
      Fingerprint.collisionCollapsesIdentityAuthorityBoundary
        (boundaryCollisionCollapseIdentityAuthorityBoundary surface)
      ≡
      false

    boundaryDigestEqualityToObjectEqualityAuthorityIsFalse :
      digestEqualityToObjectEqualityAuthority surface ≡ false

    boundaryContentAddressAuthorityIsFalse :
      contentAddressAuthority surface ≡ false

    boundarySignatureRootAuthorityIsFalse :
      signatureRootAuthority surface ≡ false

    boundaryAdversarialIntegrityAuthorityIsFalse :
      adversarialIntegrityAuthority surface ≡ false

open HashCandidateBoundaryReceipt public

canonicalHashCandidateBoundaryGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalHashCandidateBoundaryGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "hash candidate boundary receipt"
    "DASHI.Crypto.HashCandidateBoundary"
    "canonicalHashCandidateBoundaryReceipt"
    "candidate-only fingerprint projection boundary that blocks digest-equality authority"
    "digest-equality -> object-equality, content-address, signature-root, and adversarial-integrity authority stay closed"
    "agda -i . DASHI/Crypto/HashCandidateBoundary.agda"

canonicalHashCandidateBoundarySurface :
  HashCandidateBoundarySurface
canonicalHashCandidateBoundarySurface =
  mkHashCandidateBoundarySurface
    "hash candidate boundary"
    "DASHI.Crypto.HashCandidateBoundary"
    "candidate-only fingerprint projection and hash boundary"
    Fingerprint.canonicalNatFingerprintProjectionCore
    Fingerprint.canonicalCollisionCollapseIdentityAuthorityBoundary
    Fingerprint.canonicalFingerprintCollisionReceipt
    Fingerprint.canonicalFingerprintPreimageReceipt
    Fingerprint.canonicalFingerprintSecondPreimageReceipt
    canonicalHashCandidateBoundaryGenericReceipt
    false
    false
    false
    false
    "digest equality is tracked only as candidate surface information"
    "no object-equality, content-address, signature-root, or adversarial-integrity authority is promoted"

canonicalHashCandidateBoundaryReceipt :
  HashCandidateBoundaryReceipt canonicalHashCandidateBoundarySurface
canonicalHashCandidateBoundaryReceipt =
  mkHashCandidateBoundaryReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalHashCandidateBoundaryGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim
    canonicalHashCandidateBoundaryGenericReceipt
  ≡
  false
canonicalHashCandidateBoundaryGenericReceiptNonPromoting =
  refl

canonicalHashCandidateBoundaryDigestEqualityCandidateOnlyIsTrue :
  Fingerprint.digestEqualityCandidateOnly
    (boundaryCollisionCollapseIdentityAuthorityBoundary
      canonicalHashCandidateBoundarySurface)
  ≡
  true
canonicalHashCandidateBoundaryDigestEqualityCandidateOnlyIsTrue =
  boundaryDigestEqualityCandidateOnlyIsTrue
    canonicalHashCandidateBoundaryReceipt

canonicalHashCandidateBoundaryCollisionIdentityAuthorityIsFalse :
  Fingerprint.collisionCollapsesIdentityAuthorityBoundary
    (boundaryCollisionCollapseIdentityAuthorityBoundary
      canonicalHashCandidateBoundarySurface)
  ≡
  false
canonicalHashCandidateBoundaryCollisionIdentityAuthorityIsFalse =
  boundaryCollisionIdentityAuthorityIsFalse
    canonicalHashCandidateBoundaryReceipt

canonicalHashCandidateBoundaryDigestEqualityToObjectEqualityAuthorityIsFalse :
  digestEqualityToObjectEqualityAuthority
    canonicalHashCandidateBoundarySurface
  ≡
  false
canonicalHashCandidateBoundaryDigestEqualityToObjectEqualityAuthorityIsFalse =
  boundaryDigestEqualityToObjectEqualityAuthorityIsFalse
    canonicalHashCandidateBoundaryReceipt

canonicalHashCandidateBoundaryContentAddressAuthorityIsFalse :
  contentAddressAuthority
    canonicalHashCandidateBoundarySurface
  ≡
  false
canonicalHashCandidateBoundaryContentAddressAuthorityIsFalse =
  boundaryContentAddressAuthorityIsFalse
    canonicalHashCandidateBoundaryReceipt

canonicalHashCandidateBoundarySignatureRootAuthorityIsFalse :
  signatureRootAuthority
    canonicalHashCandidateBoundarySurface
  ≡
  false
canonicalHashCandidateBoundarySignatureRootAuthorityIsFalse =
  boundarySignatureRootAuthorityIsFalse
    canonicalHashCandidateBoundaryReceipt

canonicalHashCandidateBoundaryAdversarialIntegrityAuthorityIsFalse :
  adversarialIntegrityAuthority
    canonicalHashCandidateBoundarySurface
  ≡
  false
canonicalHashCandidateBoundaryAdversarialIntegrityAuthorityIsFalse =
  boundaryAdversarialIntegrityAuthorityIsFalse
    canonicalHashCandidateBoundaryReceipt
