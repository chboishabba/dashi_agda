module DASHI.Physics.Closure.ExternalAuthorityImportCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable external authority / theorem import core.
--
-- This module captures the repeated fail-closed shape:
-- an external theorem, token, or artifact is absent; the local overlap has
-- been audited; no theorem, token, import, or promotion is accepted.

data ExternalAuthorityKind : Set where
  clayExternalAuthority :
    ExternalAuthorityKind

  w4TokenExternalAuthority :
    ExternalAuthorityKind

  theoremImportExternalAuthority :
    ExternalAuthorityKind

  artifactExternalAuthority :
    ExternalAuthorityKind

record ExternalAuthorityArtifact : Set where
  constructor mkExternalAuthorityArtifact
  field
    authorityKind :
      ExternalAuthorityKind

    artifactLabel :
      String

    externalLocator :
      String

    localOverlapSummary :
      String

    artifactLocalOverlapAudited :
      Bool

    artifactLocalOverlapAuditedIsTrue :
      artifactLocalOverlapAudited ≡ true

    artifactExternalArtifactPresent :
      Bool

    artifactExternalArtifactPresentIsFalse :
      artifactExternalArtifactPresent ≡ false

    artifactTheoremPresent :
      Bool

    artifactTheoremPresentIsFalse :
      artifactTheoremPresent ≡ false

    artifactTokenPresent :
      Bool

    artifactTokenPresentIsFalse :
      artifactTokenPresent ≡ false

    artifactImportPresent :
      Bool

    artifactImportPresentIsFalse :
      artifactImportPresent ≡ false

    artifactPromoted :
      Bool

    artifactPromotedIsFalse :
      artifactPromoted ≡ false

open ExternalAuthorityArtifact public

record ExternalAuthorityImportReceipt : Set where
  constructor mkExternalAuthorityImportReceipt
  field
    receiptLabel :
      String

    artifact :
      ExternalAuthorityArtifact

    localOverlapAudited :
      Bool

    localOverlapAuditedIsTrue :
      localOverlapAudited ≡ true

    externalArtifactPresent :
      Bool

    externalArtifactPresentIsFalse :
      externalArtifactPresent ≡ false

    theoremPresent :
      Bool

    theoremPresentIsFalse :
      theoremPresent ≡ false

    tokenPresent :
      Bool

    tokenPresentIsFalse :
      tokenPresent ≡ false

    importPresent :
      Bool

    importPresentIsFalse :
      importPresent ≡ false

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    receiptNotes :
      List String

open ExternalAuthorityImportReceipt public

------------------------------------------------------------------------
-- Constructors for absent artifacts and fail-closed import receipts.

mkAbsentExternalAuthorityArtifact :
  ExternalAuthorityKind →
  String →
  String →
  String →
  ExternalAuthorityArtifact
mkAbsentExternalAuthorityArtifact kind label locator overlapSummary =
  mkExternalAuthorityArtifact
    kind
    label
    locator
    overlapSummary
    true
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

mkFailClosedExternalAuthorityImportReceipt :
  String →
  ExternalAuthorityArtifact →
  List String →
  ExternalAuthorityImportReceipt
mkFailClosedExternalAuthorityImportReceipt label artifact' notes =
  mkExternalAuthorityImportReceipt
    label
    artifact'
    (artifactLocalOverlapAudited artifact')
    (artifactLocalOverlapAuditedIsTrue artifact')
    (artifactExternalArtifactPresent artifact')
    (artifactExternalArtifactPresentIsFalse artifact')
    (artifactTheoremPresent artifact')
    (artifactTheoremPresentIsFalse artifact')
    (artifactTokenPresent artifact')
    (artifactTokenPresentIsFalse artifact')
    (artifactImportPresent artifact')
    (artifactImportPresentIsFalse artifact')
    (artifactPromoted artifact')
    (artifactPromotedIsFalse artifact')
    notes

mkAbsentFailClosedExternalAuthorityImportReceipt :
  ExternalAuthorityKind →
  String →
  String →
  String →
  String →
  List String →
  ExternalAuthorityImportReceipt
mkAbsentFailClosedExternalAuthorityImportReceipt
  kind
  receiptLabel'
  artifactLabel'
  locator
  overlapSummary
  notes =
  mkFailClosedExternalAuthorityImportReceipt
    receiptLabel'
    (mkAbsentExternalAuthorityArtifact
      kind
      artifactLabel'
      locator
      overlapSummary)
    notes

------------------------------------------------------------------------
-- Aggregate proofs over receipt lists.

data AllExternalArtifactsAbsent :
  List ExternalAuthorityImportReceipt →
  Set where
  allExternalArtifactsAbsentNil :
    AllExternalArtifactsAbsent []

  allExternalArtifactsAbsentCons :
    ∀ {receipt receipts} →
    externalArtifactPresent receipt ≡ false →
    AllExternalArtifactsAbsent receipts →
    AllExternalArtifactsAbsent (receipt ∷ receipts)

data AllExternalAuthorityPromotionsFalse :
  List ExternalAuthorityImportReceipt →
  Set where
  allExternalAuthorityPromotionsFalseNil :
    AllExternalAuthorityPromotionsFalse []

  allExternalAuthorityPromotionsFalseCons :
    ∀ {receipt receipts} →
    promoted receipt ≡ false →
    AllExternalAuthorityPromotionsFalse receipts →
    AllExternalAuthorityPromotionsFalse (receipt ∷ receipts)

proveAllExternalArtifactsAbsent :
  (receipts : List ExternalAuthorityImportReceipt) →
  AllExternalArtifactsAbsent receipts
proveAllExternalArtifactsAbsent [] =
  allExternalArtifactsAbsentNil
proveAllExternalArtifactsAbsent (receipt ∷ receipts) =
  allExternalArtifactsAbsentCons
    (externalArtifactPresentIsFalse receipt)
    (proveAllExternalArtifactsAbsent receipts)

proveAllExternalAuthorityPromotionsFalse :
  (receipts : List ExternalAuthorityImportReceipt) →
  AllExternalAuthorityPromotionsFalse receipts
proveAllExternalAuthorityPromotionsFalse [] =
  allExternalAuthorityPromotionsFalseNil
proveAllExternalAuthorityPromotionsFalse (receipt ∷ receipts) =
  allExternalAuthorityPromotionsFalseCons
    (promotedIsFalse receipt)
    (proveAllExternalAuthorityPromotionsFalse receipts)

------------------------------------------------------------------------
-- Canonical absent/fail-closed examples.

clayAbsentExternalAuthorityArtifact :
  ExternalAuthorityArtifact
clayAbsentExternalAuthorityArtifact =
  mkAbsentExternalAuthorityArtifact
    clayExternalAuthority
    "Clay external authority artifact absent"
    "Clay Mathematics Institute theorem or acceptance artifact not present in this repository"
    "Local Clay-overlap receipts were audited, but no external Clay theorem, acceptance token, import, or promotion artifact is present."

clayExternalAuthorityImportReceipt :
  ExternalAuthorityImportReceipt
clayExternalAuthorityImportReceipt =
  mkFailClosedExternalAuthorityImportReceipt
    "Clay external authority import fail-closed receipt"
    clayAbsentExternalAuthorityArtifact
    ( "local overlap audited"
    ∷ "external Clay artifact absent"
    ∷ "Clay theorem, token, import, and promotion remain false"
    ∷ []
    )

w4TokenAbsentExternalAuthorityArtifact :
  ExternalAuthorityArtifact
w4TokenAbsentExternalAuthorityArtifact =
  mkAbsentExternalAuthorityArtifact
    w4TokenExternalAuthority
    "W4 external token artifact absent"
    "W4 authority token or acceptance artifact not present in this repository"
    "Local W4-overlap was audited, but no external W4 token or promotion artifact is present."

w4TokenExternalAuthorityImportReceipt :
  ExternalAuthorityImportReceipt
w4TokenExternalAuthorityImportReceipt =
  mkFailClosedExternalAuthorityImportReceipt
    "W4 token external authority import fail-closed receipt"
    w4TokenAbsentExternalAuthorityArtifact
    ( "local W4 overlap audited"
    ∷ "external W4 token absent"
    ∷ "W4 theorem, token, import, and promotion remain false"
    ∷ []
    )

theoremImportAbsentExternalAuthorityArtifact :
  ExternalAuthorityArtifact
theoremImportAbsentExternalAuthorityArtifact =
  mkAbsentExternalAuthorityArtifact
    theoremImportExternalAuthority
    "External theorem import artifact absent"
    "External theorem library, proof term, or typed import artifact not present in this repository"
    "Local theorem-overlap was audited, but no external theorem import is accepted."

theoremImportExternalAuthorityImportReceipt :
  ExternalAuthorityImportReceipt
theoremImportExternalAuthorityImportReceipt =
  mkFailClosedExternalAuthorityImportReceipt
    "External theorem import fail-closed receipt"
    theoremImportAbsentExternalAuthorityArtifact
    ( "local theorem overlap audited"
    ∷ "external theorem artifact absent"
    ∷ "theorem, token, import, and promotion remain false"
    ∷ []
    )

canonicalExternalAuthorityImportReceipts :
  List ExternalAuthorityImportReceipt
canonicalExternalAuthorityImportReceipts =
  clayExternalAuthorityImportReceipt
  ∷ w4TokenExternalAuthorityImportReceipt
  ∷ theoremImportExternalAuthorityImportReceipt
  ∷ []

canonicalExternalAuthorityArtifactsAbsent :
  AllExternalArtifactsAbsent canonicalExternalAuthorityImportReceipts
canonicalExternalAuthorityArtifactsAbsent =
  proveAllExternalArtifactsAbsent canonicalExternalAuthorityImportReceipts

canonicalExternalAuthorityPromotionsFalse :
  AllExternalAuthorityPromotionsFalse canonicalExternalAuthorityImportReceipts
canonicalExternalAuthorityPromotionsFalse =
  proveAllExternalAuthorityPromotionsFalse
    canonicalExternalAuthorityImportReceipts

clayExternalAuthorityPromotedFalse :
  promoted clayExternalAuthorityImportReceipt
  ≡
  false
clayExternalAuthorityPromotedFalse =
  refl

w4TokenExternalAuthorityTokenFalse :
  tokenPresent w4TokenExternalAuthorityImportReceipt
  ≡
  false
w4TokenExternalAuthorityTokenFalse =
  refl

theoremImportExternalAuthorityImportFalse :
  importPresent theoremImportExternalAuthorityImportReceipt
  ≡
  false
theoremImportExternalAuthorityImportFalse =
  refl

externalAuthorityImportGenericReceipt :
  ExternalAuthorityImportReceipt →
  GenericReceipt.GenericReceipt
externalAuthorityImportGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (receiptLabel receipt)
    "DASHI.Physics.Closure.ExternalAuthorityImportCore"
    "canonicalExternalAuthorityImportReceipts"
    "external authority import receipt records local overlap as audited while external theorem, token, import, artifact, and promotion remain absent"
    "accepted external authority artifact bytes, theorem imports, tokens, and promotion gates remain missing"
    "agda -i . DASHI/Physics/Closure/ExternalAuthorityImportCore.agda"

canonicalExternalAuthorityImportGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalExternalAuthorityImportGenericReceipts =
  externalAuthorityImportGenericReceipt clayExternalAuthorityImportReceipt
  ∷ externalAuthorityImportGenericReceipt w4TokenExternalAuthorityImportReceipt
  ∷ externalAuthorityImportGenericReceipt
      theoremImportExternalAuthorityImportReceipt
  ∷ []

canonicalExternalAuthorityImportGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalExternalAuthorityImportGenericReceipts
canonicalExternalAuthorityImportGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalExternalAuthorityImportGenericReceipts
