module DASHI.Promotion.AuthorityBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Generic authority-boundary vocabulary core.
--
-- This module records blocked authority claims as canonical lists and keeps
-- every surface fail-closed.  It is reusable for bioactive, legal, physics,
-- trading, cultural, clinical, and runtime domains.  The underlying
-- candidate surface remains candidate-only, while the authority surface is
-- backed by the non-promotion core and no authority is promoted.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Boundary vocabularies.

data AuthorityBoundaryDomain : Set where
  bioactiveBoundaryDomain : AuthorityBoundaryDomain
  legalBoundaryDomain : AuthorityBoundaryDomain
  physicsBoundaryDomain : AuthorityBoundaryDomain
  tradingBoundaryDomain : AuthorityBoundaryDomain
  culturalBoundaryDomain : AuthorityBoundaryDomain
  clinicalBoundaryDomain : AuthorityBoundaryDomain
  runtimeBoundaryDomain : AuthorityBoundaryDomain

authorityBoundaryDomainName :
  AuthorityBoundaryDomain →
  String
authorityBoundaryDomainName bioactiveBoundaryDomain =
  "bioactive"
authorityBoundaryDomainName legalBoundaryDomain =
  "legal"
authorityBoundaryDomainName physicsBoundaryDomain =
  "physics"
authorityBoundaryDomainName tradingBoundaryDomain =
  "trading"
authorityBoundaryDomainName culturalBoundaryDomain =
  "cultural"
authorityBoundaryDomainName clinicalBoundaryDomain =
  "clinical"
authorityBoundaryDomainName runtimeBoundaryDomain =
  "runtime"

data AuthorityBoundaryClaimKind : Set where
  bioactiveAuthorityClaim : AuthorityBoundaryClaimKind
  legalAuthorityClaim : AuthorityBoundaryClaimKind
  physicsAuthorityClaim : AuthorityBoundaryClaimKind
  tradingAuthorityClaim : AuthorityBoundaryClaimKind
  culturalAuthorityClaim : AuthorityBoundaryClaimKind
  clinicalAuthorityClaim : AuthorityBoundaryClaimKind
  runtimeAuthorityClaim : AuthorityBoundaryClaimKind

authorityBoundaryClaimDomain :
  AuthorityBoundaryClaimKind →
  AuthorityBoundaryDomain
authorityBoundaryClaimDomain bioactiveAuthorityClaim =
  bioactiveBoundaryDomain
authorityBoundaryClaimDomain legalAuthorityClaim =
  legalBoundaryDomain
authorityBoundaryClaimDomain physicsAuthorityClaim =
  physicsBoundaryDomain
authorityBoundaryClaimDomain tradingAuthorityClaim =
  tradingBoundaryDomain
authorityBoundaryClaimDomain culturalAuthorityClaim =
  culturalBoundaryDomain
authorityBoundaryClaimDomain clinicalAuthorityClaim =
  clinicalBoundaryDomain
authorityBoundaryClaimDomain runtimeAuthorityClaim =
  runtimeBoundaryDomain

authorityBoundaryClaimName :
  AuthorityBoundaryClaimKind →
  String
authorityBoundaryClaimName bioactiveAuthorityClaim =
  "bioactive authority claim"
authorityBoundaryClaimName legalAuthorityClaim =
  "legal authority claim"
authorityBoundaryClaimName physicsAuthorityClaim =
  "physics authority claim"
authorityBoundaryClaimName tradingAuthorityClaim =
  "trading authority claim"
authorityBoundaryClaimName culturalAuthorityClaim =
  "cultural authority claim"
authorityBoundaryClaimName clinicalAuthorityClaim =
  "clinical authority claim"
authorityBoundaryClaimName runtimeAuthorityClaim =
  "runtime authority claim"

authorityBoundaryClaimAuthorityKind :
  AuthorityBoundaryClaimKind →
  AuthorityNA.AuthorityKind
authorityBoundaryClaimAuthorityKind bioactiveAuthorityClaim =
  AuthorityNA.empiricalAuthority
authorityBoundaryClaimAuthorityKind legalAuthorityClaim =
  AuthorityNA.legalAuthority
authorityBoundaryClaimAuthorityKind physicsAuthorityClaim =
  AuthorityNA.scientificAuthority
authorityBoundaryClaimAuthorityKind tradingAuthorityClaim =
  AuthorityNA.tradingAuthority
authorityBoundaryClaimAuthorityKind culturalAuthorityClaim =
  AuthorityNA.culturalAuthority
authorityBoundaryClaimAuthorityKind clinicalAuthorityClaim =
  AuthorityNA.clinicalAuthority
authorityBoundaryClaimAuthorityKind runtimeAuthorityClaim =
  AuthorityNA.runtimeAuthority

canonicalBlockedAuthorityClaims : List AuthorityBoundaryClaimKind
canonicalBlockedAuthorityClaims =
  bioactiveAuthorityClaim
  ∷ legalAuthorityClaim
  ∷ physicsAuthorityClaim
  ∷ tradingAuthorityClaim
  ∷ culturalAuthorityClaim
  ∷ clinicalAuthorityClaim
  ∷ runtimeAuthorityClaim
  ∷ []

canonicalBlockedAuthorityClaimCount : Nat
canonicalBlockedAuthorityClaimCount =
  listCount canonicalBlockedAuthorityClaims

canonicalBlockedAuthorityKinds : List AuthorityNA.AuthorityKind
canonicalBlockedAuthorityKinds =
  AuthorityNA.canonicalAuthorityKinds

canonicalBlockedAuthorityKindCount : Nat
canonicalBlockedAuthorityKindCount =
  AuthorityNA.canonicalAuthorityKindCount

------------------------------------------------------------------------
-- Authority-boundary receipt record.

record AuthorityBoundaryReceipt : Set where
  constructor mkAuthorityBoundaryReceipt
  field
    receiptLabel :
      String

    receiptDomain :
      AuthorityBoundaryDomain

    receiptClaimKind :
      AuthorityBoundaryClaimKind

    receiptClaimDomainMatches :
      receiptDomain ≡ authorityBoundaryClaimDomain receiptClaimKind

    receiptClaimAuthorityKind :
      AuthorityNA.AuthorityKind

    receiptClaimAuthorityKindMatches :
      receiptClaimAuthorityKind ≡
      authorityBoundaryClaimAuthorityKind receiptClaimKind

    receiptCandidateRow :
      CandidateOnly.CandidateOnlyRow

    receiptCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt receiptCandidateRow

    receiptAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    receiptBlockedAuthorityKinds :
      List AuthorityNA.AuthorityKind

    receiptBlockedAuthorityKindsCount :
      Nat

    receiptBlockedAuthorityKindsCountIsCanonical :
      receiptBlockedAuthorityKindsCount ≡ canonicalBlockedAuthorityKindCount

    receiptBlockedAuthorityKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        receiptAuthorityBundle
        receiptBlockedAuthorityKinds

    receiptBoundaryPromoted :
      Bool

    receiptBoundaryPromotedIsFalse :
      receiptBoundaryPromoted ≡ false

open AuthorityBoundaryReceipt public

mkFailClosedAuthorityBoundaryReceipt :
  String →
  AuthorityBoundaryDomain →
  AuthorityBoundaryClaimKind →
  CandidateOnly.CandidateOnlyKind →
  CandidateOnly.CandidateOnlyStatus →
  String →
  String →
  String →
  AuthorityBoundaryReceipt
mkFailClosedAuthorityBoundaryReceipt
  label
  domain
  claimKind
  candidateKind
  candidateStatus
  candidateStatement
  candidateGap
  candidateOwner =
  let
    candidateRow =
      CandidateOnly.mkCandidateOnlyRow
        label
        candidateOwner
        label
        candidateKind
        candidateStatus
        candidateStatement
        candidateGap

    candidateReceipt =
      CandidateOnly.canonicalCandidateOnlyReceipt
        candidateRow
        refl
        refl
        refl
        refl
        refl
        refl
        refl
        refl

    authorityBundle =
      AuthorityNA.canonicalAuthorityNonPromotionBundle
  in
  mkAuthorityBoundaryReceipt
    label
    (authorityBoundaryClaimDomain claimKind)
    claimKind
    refl
    (authorityBoundaryClaimAuthorityKind claimKind)
    refl
    candidateRow
    candidateReceipt
    authorityBundle
    canonicalBlockedAuthorityKinds
    canonicalBlockedAuthorityKindCount
    refl
    (AuthorityNA.proveAllAuthorityKindsFalse
      authorityBundle
      canonicalBlockedAuthorityKinds)
    false
    refl

------------------------------------------------------------------------
-- Projection proofs.

authorityBoundaryCandidateOnlyIsTrue :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.candidateOnly (receiptCandidateRow receipt) ≡ true
authorityBoundaryCandidateOnlyIsTrue receipt =
  CandidateOnly.candidateOnlyIsTrue
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidatePromotedIsFalse :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.promoted (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidatePromotedIsFalse receipt =
  CandidateOnly.candidatePromotedIsFalse
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidateNoTruthAuthority :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.carriesTruthAuthority (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidateNoTruthAuthority receipt =
  CandidateOnly.candidateNoTruthAuthority
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidateNoSupportAuthority :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.carriesSupportAuthority (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidateNoSupportAuthority receipt =
  CandidateOnly.candidateNoSupportAuthority
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidateNoAdmissibilityAuthority :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.carriesAdmissibilityAuthority
    (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidateNoAdmissibilityAuthority receipt =
  CandidateOnly.candidateNoAdmissibilityAuthority
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidateNoTradingAuthority :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.carriesTradingAuthority (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidateNoTradingAuthority receipt =
  CandidateOnly.candidateNoTradingAuthority
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidateNoRuntimeAuthority :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.carriesRuntimeAuthority (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidateNoRuntimeAuthority receipt =
  CandidateOnly.candidateNoRuntimeAuthority
    (receiptCandidateReceipt receipt)

authorityBoundaryCandidateNoTheoremAuthority :
  (receipt : AuthorityBoundaryReceipt) →
  CandidateOnly.carriesTheoremAuthority (receiptCandidateRow receipt) ≡ false
authorityBoundaryCandidateNoTheoremAuthority receipt =
  CandidateOnly.candidateNoTheoremAuthority
    (receiptCandidateReceipt receipt)

authorityBoundaryBundlePromotesAnyAuthorityIsFalse :
  (receipt : AuthorityBoundaryReceipt) →
  AuthorityNA.promotesAnyAuthority (receiptAuthorityBundle receipt) ≡ false
authorityBoundaryBundlePromotesAnyAuthorityIsFalse receipt =
  AuthorityNA.bundlePromotesAnyAuthorityIsFalse
    (receiptAuthorityBundle receipt)

authorityBoundaryBlockedAuthorityKindsFalse :
  (receipt : AuthorityBoundaryReceipt) →
  AuthorityNA.AllAuthorityKindsFalse
    (receiptAuthorityBundle receipt)
    (receiptBlockedAuthorityKinds receipt)
authorityBoundaryBlockedAuthorityKindsFalse receipt =
  receiptBlockedAuthorityKindsFalse receipt

authorityBoundaryClaimKindMatchesDomain :
  (receipt : AuthorityBoundaryReceipt) →
  receiptDomain receipt ≡ authorityBoundaryClaimDomain (receiptClaimKind receipt)
authorityBoundaryClaimKindMatchesDomain receipt =
  receiptClaimDomainMatches receipt

authorityBoundaryClaimKindMatchesAuthorityKind :
  (receipt : AuthorityBoundaryReceipt) →
  receiptClaimAuthorityKind receipt ≡
  authorityBoundaryClaimAuthorityKind (receiptClaimKind receipt)
authorityBoundaryClaimKindMatchesAuthorityKind receipt =
  receiptClaimAuthorityKindMatches receipt

authorityBoundaryClaimCountIsCanonical :
  canonicalBlockedAuthorityClaimCount ≡ canonicalBlockedAuthorityClaimCount
authorityBoundaryClaimCountIsCanonical =
  refl

------------------------------------------------------------------------
-- Canonical receipts.

canonicalBioactiveAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalBioactiveAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "bioactive authority boundary receipt"
    bioactiveBoundaryDomain
    bioactiveAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "bioactive authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "bioactive authority boundary status")
    "bioactive authority claims remain blocked and candidate-only"
    "bioactive promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalLegalAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalLegalAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "legal authority boundary receipt"
    legalBoundaryDomain
    legalAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "legal authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "legal authority boundary status")
    "legal authority claims remain blocked and candidate-only"
    "legal promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalPhysicsAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalPhysicsAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "physics authority boundary receipt"
    physicsBoundaryDomain
    physicsAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "physics authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "physics authority boundary status")
    "physics authority claims remain blocked and candidate-only"
    "physics promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalTradingAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalTradingAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "trading authority boundary receipt"
    tradingBoundaryDomain
    tradingAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "trading authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "trading authority boundary status")
    "trading authority claims remain blocked and candidate-only"
    "trading promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalCulturalAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalCulturalAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "cultural authority boundary receipt"
    culturalBoundaryDomain
    culturalAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "cultural authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "cultural authority boundary status")
    "cultural authority claims remain blocked and candidate-only"
    "cultural promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalClinicalAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalClinicalAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "clinical authority boundary receipt"
    clinicalBoundaryDomain
    clinicalAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "clinical authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "clinical authority boundary status")
    "clinical authority claims remain blocked and candidate-only"
    "clinical promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalRuntimeAuthorityBoundaryReceipt :
  AuthorityBoundaryReceipt
canonicalRuntimeAuthorityBoundaryReceipt =
  mkFailClosedAuthorityBoundaryReceipt
    "runtime authority boundary receipt"
    runtimeBoundaryDomain
    runtimeAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "runtime authority boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "runtime authority boundary status")
    "runtime authority claims remain blocked and candidate-only"
    "runtime promotion requires an external accepted authority bridge"
    "DASHI.Promotion.AuthorityBoundaryCore"

canonicalAuthorityBoundaryReceipts : List AuthorityBoundaryReceipt
canonicalAuthorityBoundaryReceipts =
  canonicalBioactiveAuthorityBoundaryReceipt
  ∷ canonicalLegalAuthorityBoundaryReceipt
  ∷ canonicalPhysicsAuthorityBoundaryReceipt
  ∷ canonicalTradingAuthorityBoundaryReceipt
  ∷ canonicalCulturalAuthorityBoundaryReceipt
  ∷ canonicalClinicalAuthorityBoundaryReceipt
  ∷ canonicalRuntimeAuthorityBoundaryReceipt
  ∷ []

canonicalAuthorityBoundaryReceiptCount : Nat
canonicalAuthorityBoundaryReceiptCount =
  listCount canonicalAuthorityBoundaryReceipts

data AllAuthorityBoundaryReceiptsFailClosed :
  List AuthorityBoundaryReceipt →
  Set where
  allAuthorityBoundaryReceiptsFailClosedNil :
    AllAuthorityBoundaryReceiptsFailClosed []

  allAuthorityBoundaryReceiptsFailClosedCons :
    ∀ {receipt receipts} →
    CandidateOnly.candidateOnly (receiptCandidateRow receipt) ≡ true →
    CandidateOnly.promoted (receiptCandidateRow receipt) ≡ false →
    AuthorityNA.promotesAnyAuthority (receiptAuthorityBundle receipt) ≡ false →
    AuthorityNA.AllAuthorityKindsFalse
      (receiptAuthorityBundle receipt)
      (receiptBlockedAuthorityKinds receipt) →
    AllAuthorityBoundaryReceiptsFailClosed receipts →
    AllAuthorityBoundaryReceiptsFailClosed (receipt ∷ receipts)

proveAllAuthorityBoundaryReceiptsFailClosed :
  (receipts : List AuthorityBoundaryReceipt) →
  AllAuthorityBoundaryReceiptsFailClosed receipts
proveAllAuthorityBoundaryReceiptsFailClosed [] =
  allAuthorityBoundaryReceiptsFailClosedNil
proveAllAuthorityBoundaryReceiptsFailClosed (receipt ∷ receipts) =
  allAuthorityBoundaryReceiptsFailClosedCons
    (authorityBoundaryCandidateOnlyIsTrue receipt)
    (authorityBoundaryCandidatePromotedIsFalse receipt)
    (authorityBoundaryBundlePromotesAnyAuthorityIsFalse receipt)
    (authorityBoundaryBlockedAuthorityKindsFalse receipt)
    (proveAllAuthorityBoundaryReceiptsFailClosed receipts)

canonicalAuthorityBoundaryReceiptsFailClosed :
  AllAuthorityBoundaryReceiptsFailClosed canonicalAuthorityBoundaryReceipts
canonicalAuthorityBoundaryReceiptsFailClosed =
  proveAllAuthorityBoundaryReceiptsFailClosed
    canonicalAuthorityBoundaryReceipts

------------------------------------------------------------------------
-- Generic receipt adapter.

authorityBoundaryGenericReceipt :
  AuthorityBoundaryReceipt →
  GenericReceipt.GenericReceipt
authorityBoundaryGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (receiptLabel receipt)
    "DASHI.Promotion.AuthorityBoundaryCore"
    (authorityBoundaryClaimName (receiptClaimKind receipt))
    "candidate-only row, canonical blocked authority list, and closed authority bundle are recorded"
    "no authority is promoted in this boundary core"
    "agda -i . DASHI/Promotion/AuthorityBoundaryCore.agda"

canonicalAuthorityBoundaryGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalAuthorityBoundaryGenericReceipts =
  authorityBoundaryGenericReceipt canonicalBioactiveAuthorityBoundaryReceipt
  ∷ authorityBoundaryGenericReceipt canonicalLegalAuthorityBoundaryReceipt
  ∷ authorityBoundaryGenericReceipt canonicalPhysicsAuthorityBoundaryReceipt
  ∷ authorityBoundaryGenericReceipt canonicalTradingAuthorityBoundaryReceipt
  ∷ authorityBoundaryGenericReceipt canonicalCulturalAuthorityBoundaryReceipt
  ∷ authorityBoundaryGenericReceipt canonicalClinicalAuthorityBoundaryReceipt
  ∷ authorityBoundaryGenericReceipt canonicalRuntimeAuthorityBoundaryReceipt
  ∷ []

canonicalAuthorityBoundaryGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalAuthorityBoundaryGenericReceipts
canonicalAuthorityBoundaryGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalAuthorityBoundaryGenericReceipts
