module DASHI.Interop.PNFPackageCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Interop.ResidualBoundaryCore as Boundary

------------------------------------------------------------------------
-- Reusable PNF package refs.
--
-- This module is a small reusable query/resolver/selector package core.
-- It carries only typed references, residual boundary metadata, rejection
-- metadata, and fail-closed admission invariants.  Candidate-only packages
-- remain non-admitted; admitted packages must carry object/span/receipt refs.

data PNFObjectRef : Set where
  pnfObjectRef :
    Nat →
    PNFObjectRef

  pnfObjectFallback :
    PNFObjectRef

data SpanRef : Set where
  spanRef :
    Nat →
    SpanRef

  spanFallback :
    SpanRef

data ReceiptRef : Set where
  receiptRef :
    Nat →
    ReceiptRef

  receiptFallback :
    ReceiptRef

data QueryRef : Set where
  queryRef :
    Nat →
    QueryRef

  queryFallback :
    QueryRef

data PackageRef : Set where
  packageRef :
    Nat →
    PackageRef

  packageFallback :
    PackageRef

------------------------------------------------------------------------
-- Query and rejection vocabulary.

data QueryMode : Set where
  exactObjectLookup :
    QueryMode

  residualNeighborhoodLookup :
    QueryMode

  hybridPNFNavigation :
    QueryMode

  selectorAdmissionRequest :
    QueryMode

  packageCommitmentRequest :
    QueryMode

canonicalQueryModes : List QueryMode
canonicalQueryModes =
  exactObjectLookup
  ∷ residualNeighborhoodLookup
  ∷ hybridPNFNavigation
  ∷ selectorAdmissionRequest
  ∷ packageCommitmentRequest
  ∷ []

data RejectionReason : Set where
  noRejection :
    RejectionReason

  unresolvedCandidate :
    RejectionReason

  missingObjectRef :
    RejectionReason

  missingSpanRef :
    RejectionReason

  missingReceiptRef :
    RejectionReason

  contradictionRequiresReceipt :
    RejectionReason

  residualNotAdmissible :
    RejectionReason

  scoreClaimedAsAuthority :
    RejectionReason

  directCandidateCommitment :
    RejectionReason

canonicalRejectionReasons : List RejectionReason
canonicalRejectionReasons =
  unresolvedCandidate
  ∷ missingObjectRef
  ∷ missingSpanRef
  ∷ missingReceiptRef
  ∷ contradictionRequiresReceipt
  ∷ residualNotAdmissible
  ∷ scoreClaimedAsAuthority
  ∷ directCandidateCommitment
  ∷ []

data PackageAdmissionStatus : Set where
  candidateOnlyStatus :
    PackageAdmissionStatus

  admittedStatus :
    PackageAdmissionStatus

  rejectedStatus :
    PackageAdmissionStatus

  failClosedStatus :
    PackageAdmissionStatus

------------------------------------------------------------------------
-- Fail-closed invariant surface.

notBool :
  Bool →
  Bool
notBool true =
  false
notBool false =
  true

_&&_ :
  Bool →
  Bool →
  Bool
true && right =
  right
false && _ =
  false

infixr 6 _&&_

packageAdmissionInvariant :
  PackageAdmissionStatus →
  Bool →
  Bool →
  Bool →
  Bool →
  Bool →
  Bool →
  Bool
packageAdmissionInvariant
  candidateOnlyStatus
  candidateOnly
  _
  _
  _
  admitted
  failClosed =
  candidateOnly && notBool admitted && failClosed
packageAdmissionInvariant
  admittedStatus
  candidateOnly
  hasObjectRef
  hasSpanRef
  hasReceiptRef
  admitted
  failClosed =
  notBool candidateOnly
  && hasObjectRef
  && hasSpanRef
  && hasReceiptRef
  && admitted
  && notBool failClosed
packageAdmissionInvariant
  rejectedStatus
  _
  _
  _
  _
  admitted
  failClosed =
  notBool admitted && failClosed
packageAdmissionInvariant
  failClosedStatus
  _
  _
  _
  _
  admitted
  failClosed =
  notBool admitted && failClosed

candidateOnlyInvariant :
  Bool →
  Bool →
  Bool
candidateOnlyInvariant admitted failClosed =
  notBool admitted && failClosed

admittedRequiresRefs :
  Bool →
  Bool →
  Bool →
  Bool →
  Bool
admittedRequiresRefs hasObjectRef hasSpanRef hasReceiptRef admitted =
  hasObjectRef && hasSpanRef && hasReceiptRef && admitted

candidateOnlyFailsClosed :
  candidateOnlyInvariant false true ≡ true
candidateOnlyFailsClosed =
  refl

admittedRefsSucceed :
  admittedRequiresRefs true true true true ≡ true
admittedRefsSucceed =
  refl

candidateOnlyStatusFailsClosed :
  packageAdmissionInvariant
    candidateOnlyStatus
    true
    false
    false
    false
    false
    true
  ≡
  true
candidateOnlyStatusFailsClosed =
  refl

admittedStatusRequiresRefs :
  packageAdmissionInvariant
    admittedStatus
    false
    true
    true
    true
    true
    false
  ≡
  true
admittedStatusRequiresRefs =
  refl

------------------------------------------------------------------------
-- Query, resolver, and selector records.

record PNFQuery : Set where
  constructor pnfQuery
  field
    query :
      QueryRef

    queryMode :
      QueryMode

    queryObject :
      PNFObjectRef

    querySpan :
      SpanRef

    queryReceipt :
      ReceiptRef

    queryCandidateOnly :
      Bool

    queryAdmitted :
      Bool

    queryFailClosed :
      Bool

    queryFailClosedInvariant :
      candidateOnlyInvariant queryAdmitted queryFailClosed ≡ true

open PNFQuery public

record ResolverResult : Set where
  constructor resolverResult
  field
    resolverQuery :
      PNFQuery

    resolvedObject :
      PNFObjectRef

    resolvedSpan :
      SpanRef

    resolverReceipt :
      ReceiptRef

    resolverResidual :
      Boundary.BoundaryResidual

    resolverContradictionRecorded :
      Bool

    resolverRejectionReason :
      RejectionReason

    resolverStatus :
      PackageAdmissionStatus

    resolverCandidateOnly :
      Bool

    resolverHasObjectRef :
      Bool

    resolverHasSpanRef :
      Bool

    resolverHasReceiptRef :
      Bool

    resolverAdmitted :
      Bool

    resolverFailClosed :
      Bool

    resolverPromotesCandidateSupport :
      Bool

    resolverUsesScoreAsAuthority :
      Bool

    resolverInvariant :
      packageAdmissionInvariant
        resolverStatus
        resolverCandidateOnly
        resolverHasObjectRef
        resolverHasSpanRef
        resolverHasReceiptRef
        resolverAdmitted
        resolverFailClosed
      ≡
      true

    resolverPromotesCandidateSupportIsFalse :
      resolverPromotesCandidateSupport ≡ false

    resolverUsesScoreAsAuthorityIsFalse :
      resolverUsesScoreAsAuthority ≡ false

open ResolverResult public

record SelectorPackage : Set where
  constructor selectorPackage
  field
    selectorPackageRef :
      PackageRef

    selectorResolver :
      ResolverResult

    selectedObject :
      PNFObjectRef

    selectedSpan :
      SpanRef

    selectorReceipt :
      ReceiptRef

    selectorResidual :
      Boundary.BoundaryResidual

    selectorContradictionReceipt :
      ReceiptRef

    selectorContradictionRecorded :
      Bool

    selectorRejectionReason :
      RejectionReason

    selectorStatus :
      PackageAdmissionStatus

    selectorCandidateOnly :
      Bool

    selectorHasObjectRef :
      Bool

    selectorHasSpanRef :
      Bool

    selectorHasReceiptRef :
      Bool

    selectorAdmitted :
      Bool

    selectorFailClosed :
      Bool

    selectorPromotesCandidateSupport :
      Bool

    selectorCommitsDirectlyToITIR :
      Bool

    selectorInvariant :
      packageAdmissionInvariant
        selectorStatus
        selectorCandidateOnly
        selectorHasObjectRef
        selectorHasSpanRef
        selectorHasReceiptRef
        selectorAdmitted
        selectorFailClosed
      ≡
      true

    selectorPromotesCandidateSupportIsFalse :
      selectorPromotesCandidateSupport ≡ false

    selectorCommitsDirectlyToITIRIsFalse :
      selectorCommitsDirectlyToITIR ≡ false

open SelectorPackage public

------------------------------------------------------------------------
-- Canonical resolver/selector receipt examples.

canonicalCandidateOnlyQuery :
  PNFQuery
canonicalCandidateOnlyQuery =
  pnfQuery
    queryFallback
    hybridPNFNavigation
    pnfObjectFallback
    spanFallback
    receiptFallback
    true
    false
    true
    refl

canonicalCandidateOnlyResolverResult :
  ResolverResult
canonicalCandidateOnlyResolverResult =
  resolverResult
    canonicalCandidateOnlyQuery
    pnfObjectFallback
    spanFallback
    receiptFallback
    Boundary.noTypedMeet
    false
    unresolvedCandidate
    candidateOnlyStatus
    true
    false
    false
    false
    false
    true
    false
    false
    refl
    refl
    refl

canonicalAdmittedQuery :
  PNFQuery
canonicalAdmittedQuery =
  pnfQuery
    (queryRef 1)
    exactObjectLookup
    (pnfObjectRef 1)
    (spanRef 1)
    (receiptRef 1)
    false
    false
    true
    refl

canonicalAdmittedResolverResult :
  ResolverResult
canonicalAdmittedResolverResult =
  resolverResult
    canonicalAdmittedQuery
    (pnfObjectRef 1)
    (spanRef 1)
    (receiptRef 2)
    Boundary.exact
    false
    noRejection
    admittedStatus
    false
    true
    true
    true
    true
    false
    false
    false
    refl
    refl
    refl

canonicalCandidateOnlySelectorPackage :
  SelectorPackage
canonicalCandidateOnlySelectorPackage =
  selectorPackage
    packageFallback
    canonicalCandidateOnlyResolverResult
    pnfObjectFallback
    spanFallback
    receiptFallback
    Boundary.noTypedMeet
    receiptFallback
    false
    unresolvedCandidate
    candidateOnlyStatus
    true
    false
    false
    false
    false
    true
    false
    false
    refl
    refl
    refl

canonicalAdmittedSelectorPackage :
  SelectorPackage
canonicalAdmittedSelectorPackage =
  selectorPackage
    (packageRef 1)
    canonicalAdmittedResolverResult
    (pnfObjectRef 1)
    (spanRef 1)
    (receiptRef 3)
    Boundary.exact
    (receiptRef 4)
    false
    noRejection
    admittedStatus
    false
    true
    true
    true
    true
    false
    false
    false
    refl
    refl
    refl

canonicalResolverReceiptExamples :
  List ResolverResult
canonicalResolverReceiptExamples =
  canonicalCandidateOnlyResolverResult
  ∷ canonicalAdmittedResolverResult
  ∷ []

canonicalSelectorReceiptExamples :
  List SelectorPackage
canonicalSelectorReceiptExamples =
  canonicalCandidateOnlySelectorPackage
  ∷ canonicalAdmittedSelectorPackage
  ∷ []

selectorPackageGenericReceipt :
  SelectorPackage →
  GenericReceipt.GenericReceipt
selectorPackageGenericReceipt package =
  GenericReceipt.mkNonPromotingReceipt
    "PNF resolver selector package core"
    "DASHI.Interop.PNFPackageCore"
    "canonicalSelectorReceiptExamples"
    "PNF query, resolver, selector, span, receipt, residual, contradiction, and rejection metadata are factored into reusable package rows"
    "candidate-only and rejected packages remain fail-closed; admitted examples are local package-shape receipts, not ITIR runtime authority"
    "agda -i . DASHI/Interop/PNFPackageCore.agda"

canonicalPNFPackageGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalPNFPackageGenericReceipts =
  selectorPackageGenericReceipt canonicalCandidateOnlySelectorPackage
  ∷ selectorPackageGenericReceipt canonicalAdmittedSelectorPackage
  ∷ []

canonicalPNFPackageGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalPNFPackageGenericReceipts
canonicalPNFPackageGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalPNFPackageGenericReceipts
