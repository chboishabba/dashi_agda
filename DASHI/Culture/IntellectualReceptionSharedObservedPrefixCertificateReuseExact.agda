module DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / SHARED-OBSERVED-PREFIX CERTIFICATE REUSE
--
-- Two fine histories may agree through a chosen finite observation precision
-- while differing in a hidden coordinate.  Certificate reuse is permitted only
-- when every coordinate in the certificate support is among the coordinates
-- proved shared at that observation precision.
--
-- This is a DASHI support/reuse calculus.  It borrows only the structural
-- shared-prefix lesson from the p-adic/radix and floating-representation lanes;
-- it is not a p-adic identity, a Float equality theorem, or a claim that coarse
-- agreement reconstructs the fine histories.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreExact as Fibre
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal
import DASHI.Culture.IntellectualReceptionPadicFloatingRepresentationBoundaryExact as PadicFloat

------------------------------------------------------------------------
-- 1. The chosen finite observation precision through t1.
------------------------------------------------------------------------

data PrefixCoordinate : Set where
  presentCoordinate
  futureCoordinate
  authorityCoordinate
  : PrefixCoordinate

record SharedObservedPrefixThroughT1 : Set where
  constructor shared-observed-prefix-through-t1
  field
    samePresentAtT1 :
      Fibre.present
        (Fibre.fibreAt
          Temporal.movementEarlyAuthorityHistory
          Temporal.t1)
      ≡ Fibre.present
        (Fibre.fibreAt
          Temporal.movementLateAuthorityHistory
          Temporal.t1)

    sameFutureAtT1 :
      Fibre.futureCone
        (Fibre.fibreAt
          Temporal.movementEarlyAuthorityHistory
          Temporal.t1)
      ≡ Fibre.futureCone
        (Fibre.fibreAt
          Temporal.movementLateAuthorityHistory
          Temporal.t1)

open SharedObservedPrefixThroughT1 public

canonicalSharedObservedPrefixThroughT1 : SharedObservedPrefixThroughT1
canonicalSharedObservedPrefixThroughT1 =
  shared-observed-prefix-through-t1
    Fibre.samePresent
    Fibre.sameFutureCone

------------------------------------------------------------------------
-- 2. Sharedness is coordinate-sensitive, not a whole-fibre equality.
------------------------------------------------------------------------

data SharedAtT1Precision : PrefixCoordinate → Set where
  presentShared : SharedAtT1Precision presentCoordinate
  futureShared : SharedAtT1Precision futureCoordinate

authorityNotSharedAtT1 : SharedAtT1Precision authorityCoordinate → ⊥
authorityNotSharedAtT1 ()

authorityReallyDiffersAtT1 :
  Fibre.authorityEnabled
    (Fibre.fibreAt
      Temporal.movementEarlyAuthorityHistory
      Temporal.t1)
  ≡ Fibre.authorityEnabled
    (Fibre.fibreAt
      Temporal.movementLateAuthorityHistory
      Temporal.t1) → ⊥
authorityReallyDiffersAtT1 =
  Fibre.authorityAdmissibilityDiffersInsideSameCoarseFibre

------------------------------------------------------------------------
-- 3. Certificate support is explicit.
------------------------------------------------------------------------

data CertificateSupport : Set where
  presentFutureSupport
  authoritySensitiveSupport
  : CertificateSupport

data SupportedCoordinate : CertificateSupport → PrefixCoordinate → Set where
  supportPresent :
    ∀ {support} →
    SupportedCoordinate support presentCoordinate

  supportFuture :
    ∀ {support} →
    SupportedCoordinate support futureCoordinate

  supportAuthority :
    SupportedCoordinate authoritySensitiveSupport authorityCoordinate

SupportContainedInSharedPrefix : CertificateSupport → Set
SupportContainedInSharedPrefix support =
  ∀ {coordinate} →
  SupportedCoordinate support coordinate →
  SharedAtT1Precision coordinate

presentFutureSupportContained :
  SupportContainedInSharedPrefix presentFutureSupport
presentFutureSupportContained supportPresent = presentShared
presentFutureSupportContained supportFuture = futureShared

authoritySensitiveSupportNotContained :
  SupportContainedInSharedPrefix authoritySensitiveSupport → ⊥
authoritySensitiveSupportNotContained contained =
  authorityNotSharedAtT1 (contained supportAuthority)

------------------------------------------------------------------------
-- 4. Reuse is generated only from a support-containment receipt.
------------------------------------------------------------------------

data CertificateReusableAcrossEarlyLate : CertificateSupport → Set where
  reuseFromSharedSupport :
    ∀ {support} →
    SupportContainedInSharedPrefix support →
    CertificateReusableAcrossEarlyLate support

presentFutureCertificateReusable :
  CertificateReusableAcrossEarlyLate presentFutureSupport
presentFutureCertificateReusable =
  reuseFromSharedSupport presentFutureSupportContained

authoritySensitiveCertificateNotReusable :
  CertificateReusableAcrossEarlyLate authoritySensitiveSupport → ⊥
authoritySensitiveCertificateNotReusable
  (reuseFromSharedSupport contained) =
  authoritySensitiveSupportNotContained contained

------------------------------------------------------------------------
-- 5. Generic least-privilege reuse theorem for this precision.
------------------------------------------------------------------------

reuseIfSupportContainedInSharedPrefix :
  (support : CertificateSupport) →
  SupportContainedInSharedPrefix support →
  CertificateReusableAcrossEarlyLate support
reuseIfSupportContainedInSharedPrefix support contained =
  reuseFromSharedSupport contained

------------------------------------------------------------------------
-- 6. The p-adic/floating cross-pollination is structural only.
------------------------------------------------------------------------

coarseDisplayAlreadyKnownToHideFinePrefix :
  PadicFloat.ReceptionPadicFloatingCrossPollination
coarseDisplayAlreadyKnownToHideFinePrefix =
  PadicFloat.canonicalReceptionPadicFloatingCrossPollination

data SharedObservedPrefixPromotesFineHistoryEquality : Set where
data SharedObservedPrefixPromotesPAdicEquality : Set where
data SharedObservedPrefixPromotesFloatEquality : Set where

sharedObservedPrefixDoesNotPromoteFineHistoryEquality :
  SharedObservedPrefixPromotesFineHistoryEquality → ⊥
sharedObservedPrefixDoesNotPromoteFineHistoryEquality ()

sharedObservedPrefixDoesNotPromotePAdicEquality :
  SharedObservedPrefixPromotesPAdicEquality → ⊥
sharedObservedPrefixDoesNotPromotePAdicEquality ()

sharedObservedPrefixDoesNotPromoteFloatEquality :
  SharedObservedPrefixPromotesFloatEquality → ⊥
sharedObservedPrefixDoesNotPromoteFloatEquality ()

------------------------------------------------------------------------
-- 7. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionSharedObservedPrefixCertificateReuseBoundary : Set where
  constructor intellectual-reception-shared-observed-prefix-certificate-reuse-boundary
  field
    observationPrecisionIsExplicit : Bool
    presentAndFutureAreSharedAtT1Precision : Bool
    authorityIsSharedAtT1Precision : Bool
    certificateSupportIsExplicit : Bool
    containedSupportPermitsReuse : Bool
    authoritySensitiveSupportPermitsReuse : Bool
    sharedObservedPrefixDeterminesFineHistory : Bool
    sharedObservedPrefixIsLiteralPAdicEquality : Bool
    sharedObservedPrefixIsFloatEquality : Bool
    sourceAttributionBoundarySurvivesReuseReasoning : Bool

canonicalIntellectualReceptionSharedObservedPrefixCertificateReuseBoundary :
  IntellectualReceptionSharedObservedPrefixCertificateReuseBoundary
canonicalIntellectualReceptionSharedObservedPrefixCertificateReuseBoundary =
  intellectual-reception-shared-observed-prefix-certificate-reuse-boundary
    true true false true true false false false false true
