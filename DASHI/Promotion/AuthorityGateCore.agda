module DASHI.Promotion.AuthorityGateCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable fail-closed authority / promotion-gate core.
--
-- A local formal artifact may be catalogued, replayed, or inspected, but
-- it does not promote into an authority-bearing claim for any domain below
-- unless an external domain authority gate is supplied.  This core records
-- the local default: every canonical gate is closed and every promotion bit
-- is false.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Authority vocabulary.

data AuthorityKind : Set where
  empiricalAuthority : AuthorityKind
  legalAuthority : AuthorityKind
  clinicalAuthority : AuthorityKind
  scientificAuthority : AuthorityKind
  spiritualAuthority : AuthorityKind
  culturalAuthority : AuthorityKind
  tradingAuthority : AuthorityKind
  supportAuthority : AuthorityKind
  admissibilityAuthority : AuthorityKind
  theoremAuthority : AuthorityKind
  clayAuthority : AuthorityKind
  runtimeAuthority : AuthorityKind

AuthorityDomain : Set
AuthorityDomain = AuthorityKind

canonicalAuthorityKinds : List AuthorityKind
canonicalAuthorityKinds =
  empiricalAuthority
  ∷ legalAuthority
  ∷ clinicalAuthority
  ∷ scientificAuthority
  ∷ spiritualAuthority
  ∷ culturalAuthority
  ∷ tradingAuthority
  ∷ supportAuthority
  ∷ admissibilityAuthority
  ∷ theoremAuthority
  ∷ clayAuthority
  ∷ runtimeAuthority
  ∷ []

canonicalAuthorityKindCount : Nat
canonicalAuthorityKindCount =
  listCount canonicalAuthorityKinds

------------------------------------------------------------------------
-- Gate and receipt records.

record PromotionGate : Set where
  constructor mkPromotionGate
  field
    authorityKind :
      AuthorityKind

    gateLabel :
      String

    localGate :
      Bool

    localGateIsFalse :
      localGate ≡ false

    externalAuthoritySupplied :
      Bool

    externalAuthoritySuppliedIsFalse :
      externalAuthoritySupplied ≡ false

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open PromotionGate public

record AuthorityGateReceipt : Set where
  constructor mkAuthorityGateReceipt
  field
    receiptLabel :
      String

    gate :
      PromotionGate

    receiptAuthorityKind :
      AuthorityKind

    receiptAuthorityKindMatches :
      receiptAuthorityKind ≡ authorityKind gate

    receiptLocalGateIsFalse :
      localGate gate ≡ false

    receiptExternalAuthoritySuppliedIsFalse :
      externalAuthoritySupplied gate ≡ false

    receiptPromotedIsFalse :
      promoted gate ≡ false

open AuthorityGateReceipt public

------------------------------------------------------------------------
-- Generic fail-closed constructors and proofs.

mkClosedGate :
  AuthorityKind →
  String →
  PromotionGate
mkClosedGate kind label =
  mkPromotionGate
    kind
    label
    false
    refl
    false
    refl
    false
    refl

mkClosedReceipt :
  String →
  PromotionGate →
  AuthorityGateReceipt
mkClosedReceipt label gate =
  mkAuthorityGateReceipt
    label
    gate
    (authorityKind gate)
    refl
    (localGateIsFalse gate)
    (externalAuthoritySuppliedIsFalse gate)
    (promotedIsFalse gate)

authorityGateGenericReceipt :
  AuthorityGateReceipt →
  GenericReceipt.GenericReceipt
authorityGateGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (receiptLabel receipt)
    "DASHI.Promotion.AuthorityGateCore"
    "canonicalAuthorityGateReceipts"
    "closed authority gate receipt records local gate, external authority supplied, and promoted bits as false"
    "domain-specific external authority artifacts remain absent unless supplied by a separate accepted gate"
    "agda -i . DASHI/Promotion/AuthorityGateCore.agda"

data AllLocalGatesFalse : List PromotionGate → Set where
  allLocalGatesFalseNil :
    AllLocalGatesFalse []

  allLocalGatesFalseCons :
    ∀ {gate gates} →
    localGate gate ≡ false →
    AllLocalGatesFalse gates →
    AllLocalGatesFalse (gate ∷ gates)

proveAllLocalGatesFalse :
  (gates : List PromotionGate) →
  AllLocalGatesFalse gates
proveAllLocalGatesFalse [] =
  allLocalGatesFalseNil
proveAllLocalGatesFalse (gate ∷ gates) =
  allLocalGatesFalseCons
    (localGateIsFalse gate)
    (proveAllLocalGatesFalse gates)

data AllPromotionsFalse : List PromotionGate → Set where
  allPromotionsFalseNil :
    AllPromotionsFalse []

  allPromotionsFalseCons :
    ∀ {gate gates} →
    promoted gate ≡ false →
    AllPromotionsFalse gates →
    AllPromotionsFalse (gate ∷ gates)

proveAllPromotionsFalse :
  (gates : List PromotionGate) →
  AllPromotionsFalse gates
proveAllPromotionsFalse [] =
  allPromotionsFalseNil
proveAllPromotionsFalse (gate ∷ gates) =
  allPromotionsFalseCons
    (promotedIsFalse gate)
    (proveAllPromotionsFalse gates)

data AllReceiptLocalGatesFalse : List AuthorityGateReceipt → Set where
  allReceiptLocalGatesFalseNil :
    AllReceiptLocalGatesFalse []

  allReceiptLocalGatesFalseCons :
    ∀ {receipt receipts} →
    localGate (gate receipt) ≡ false →
    AllReceiptLocalGatesFalse receipts →
    AllReceiptLocalGatesFalse (receipt ∷ receipts)

proveAllReceiptLocalGatesFalse :
  (receipts : List AuthorityGateReceipt) →
  AllReceiptLocalGatesFalse receipts
proveAllReceiptLocalGatesFalse [] =
  allReceiptLocalGatesFalseNil
proveAllReceiptLocalGatesFalse (receipt ∷ receipts) =
  allReceiptLocalGatesFalseCons
    (receiptLocalGateIsFalse receipt)
    (proveAllReceiptLocalGatesFalse receipts)

------------------------------------------------------------------------
-- Canonical gates.

empiricalPromotionGate : PromotionGate
empiricalPromotionGate =
  mkClosedGate empiricalAuthority "empirical authority gate"

legalPromotionGate : PromotionGate
legalPromotionGate =
  mkClosedGate legalAuthority "legal authority gate"

clinicalPromotionGate : PromotionGate
clinicalPromotionGate =
  mkClosedGate clinicalAuthority "clinical authority gate"

scientificPromotionGate : PromotionGate
scientificPromotionGate =
  mkClosedGate scientificAuthority "scientific authority gate"

spiritualPromotionGate : PromotionGate
spiritualPromotionGate =
  mkClosedGate spiritualAuthority "spiritual authority gate"

culturalPromotionGate : PromotionGate
culturalPromotionGate =
  mkClosedGate culturalAuthority "cultural authority gate"

tradingPromotionGate : PromotionGate
tradingPromotionGate =
  mkClosedGate tradingAuthority "trading authority gate"

supportPromotionGate : PromotionGate
supportPromotionGate =
  mkClosedGate supportAuthority "support authority gate"

admissibilityPromotionGate : PromotionGate
admissibilityPromotionGate =
  mkClosedGate admissibilityAuthority "admissibility authority gate"

theoremPromotionGate : PromotionGate
theoremPromotionGate =
  mkClosedGate theoremAuthority "theorem authority gate"

clayPromotionGate : PromotionGate
clayPromotionGate =
  mkClosedGate clayAuthority "Clay authority gate"

runtimePromotionGate : PromotionGate
runtimePromotionGate =
  mkClosedGate runtimeAuthority "runtime authority gate"

canonicalPromotionGates : List PromotionGate
canonicalPromotionGates =
  empiricalPromotionGate
  ∷ legalPromotionGate
  ∷ clinicalPromotionGate
  ∷ scientificPromotionGate
  ∷ spiritualPromotionGate
  ∷ culturalPromotionGate
  ∷ tradingPromotionGate
  ∷ supportPromotionGate
  ∷ admissibilityPromotionGate
  ∷ theoremPromotionGate
  ∷ clayPromotionGate
  ∷ runtimePromotionGate
  ∷ []

canonicalPromotionGateCount : Nat
canonicalPromotionGateCount =
  listCount canonicalPromotionGates

canonicalPromotionGatesLocalFalse :
  AllLocalGatesFalse canonicalPromotionGates
canonicalPromotionGatesLocalFalse =
  proveAllLocalGatesFalse canonicalPromotionGates

canonicalPromotionGatesPromotedFalse :
  AllPromotionsFalse canonicalPromotionGates
canonicalPromotionGatesPromotedFalse =
  proveAllPromotionsFalse canonicalPromotionGates

------------------------------------------------------------------------
-- Canonical receipts.

empiricalAuthorityGateReceipt : AuthorityGateReceipt
empiricalAuthorityGateReceipt =
  mkClosedReceipt "empirical authority gate receipt" empiricalPromotionGate

legalAuthorityGateReceipt : AuthorityGateReceipt
legalAuthorityGateReceipt =
  mkClosedReceipt "legal authority gate receipt" legalPromotionGate

clinicalAuthorityGateReceipt : AuthorityGateReceipt
clinicalAuthorityGateReceipt =
  mkClosedReceipt "clinical authority gate receipt" clinicalPromotionGate

scientificAuthorityGateReceipt : AuthorityGateReceipt
scientificAuthorityGateReceipt =
  mkClosedReceipt "scientific authority gate receipt" scientificPromotionGate

spiritualAuthorityGateReceipt : AuthorityGateReceipt
spiritualAuthorityGateReceipt =
  mkClosedReceipt "spiritual authority gate receipt" spiritualPromotionGate

culturalAuthorityGateReceipt : AuthorityGateReceipt
culturalAuthorityGateReceipt =
  mkClosedReceipt "cultural authority gate receipt" culturalPromotionGate

tradingAuthorityGateReceipt : AuthorityGateReceipt
tradingAuthorityGateReceipt =
  mkClosedReceipt "trading authority gate receipt" tradingPromotionGate

supportAuthorityGateReceipt : AuthorityGateReceipt
supportAuthorityGateReceipt =
  mkClosedReceipt "support authority gate receipt" supportPromotionGate

admissibilityAuthorityGateReceipt : AuthorityGateReceipt
admissibilityAuthorityGateReceipt =
  mkClosedReceipt
    "admissibility authority gate receipt"
    admissibilityPromotionGate

theoremAuthorityGateReceipt : AuthorityGateReceipt
theoremAuthorityGateReceipt =
  mkClosedReceipt "theorem authority gate receipt" theoremPromotionGate

clayAuthorityGateReceipt : AuthorityGateReceipt
clayAuthorityGateReceipt =
  mkClosedReceipt "Clay authority gate receipt" clayPromotionGate

runtimeAuthorityGateReceipt : AuthorityGateReceipt
runtimeAuthorityGateReceipt =
  mkClosedReceipt "runtime authority gate receipt" runtimePromotionGate

canonicalAuthorityGateReceipts : List AuthorityGateReceipt
canonicalAuthorityGateReceipts =
  empiricalAuthorityGateReceipt
  ∷ legalAuthorityGateReceipt
  ∷ clinicalAuthorityGateReceipt
  ∷ scientificAuthorityGateReceipt
  ∷ spiritualAuthorityGateReceipt
  ∷ culturalAuthorityGateReceipt
  ∷ tradingAuthorityGateReceipt
  ∷ supportAuthorityGateReceipt
  ∷ admissibilityAuthorityGateReceipt
  ∷ theoremAuthorityGateReceipt
  ∷ clayAuthorityGateReceipt
  ∷ runtimeAuthorityGateReceipt
  ∷ []

canonicalAuthorityGateReceiptCount : Nat
canonicalAuthorityGateReceiptCount =
  listCount canonicalAuthorityGateReceipts

canonicalAuthorityGateReceiptsLocalFalse :
  AllReceiptLocalGatesFalse canonicalAuthorityGateReceipts
canonicalAuthorityGateReceiptsLocalFalse =
  proveAllReceiptLocalGatesFalse canonicalAuthorityGateReceipts

canonicalAuthorityGateGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalAuthorityGateGenericReceipts =
  authorityGateGenericReceipt empiricalAuthorityGateReceipt
  ∷ authorityGateGenericReceipt legalAuthorityGateReceipt
  ∷ authorityGateGenericReceipt clinicalAuthorityGateReceipt
  ∷ authorityGateGenericReceipt scientificAuthorityGateReceipt
  ∷ authorityGateGenericReceipt spiritualAuthorityGateReceipt
  ∷ authorityGateGenericReceipt culturalAuthorityGateReceipt
  ∷ authorityGateGenericReceipt tradingAuthorityGateReceipt
  ∷ authorityGateGenericReceipt supportAuthorityGateReceipt
  ∷ authorityGateGenericReceipt admissibilityAuthorityGateReceipt
  ∷ authorityGateGenericReceipt theoremAuthorityGateReceipt
  ∷ authorityGateGenericReceipt clayAuthorityGateReceipt
  ∷ authorityGateGenericReceipt runtimeAuthorityGateReceipt
  ∷ []

canonicalAuthorityGateGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalAuthorityGateGenericReceipts
canonicalAuthorityGateGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalAuthorityGateGenericReceipts
