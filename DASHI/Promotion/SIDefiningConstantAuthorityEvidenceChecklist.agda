module DASHI.Promotion.SIDefiningConstantAuthorityEvidenceChecklist where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload
import DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest as SIArtifact
import DASHI.Promotion.SIExactConstantParsedCarrierRequest as Parsed

------------------------------------------------------------------------
-- Evidence checklist for exact SI defining constants.
--
-- The artifact request module names the BIPM/NIST rows, and the parsed
-- carrier request module supplies structural Nat/decimal carriers.  This
-- module records the authority-evidence checklist between those layers:
-- every evidence socket is named, every source ref is explicit, and every
-- authority/promotion gate remains false.  It does not invent an artifact
-- identity, SHA-256 digest, access date, authority token, or ingestion
-- receipt.

data SIConstantAuthorityEvidenceField : Set where
  authorityArtifactIdentityField :
    SIConstantAuthorityEvidenceField
  authorityArtifactSha256Field :
    SIConstantAuthorityEvidenceField
  authorityAccessDateEvidenceField :
    SIConstantAuthorityEvidenceField
  rawNumericTextField :
    SIConstantAuthorityEvidenceField
  rawUncertaintyTextField :
    SIConstantAuthorityEvidenceField
  parsedCarrierPayloadField :
    SIConstantAuthorityEvidenceField
  covarianceOrIndependenceReceiptField :
    SIConstantAuthorityEvidenceField
  consumerIngestionReceiptField :
    SIConstantAuthorityEvidenceField

data SIConstantAuthorityEvidenceState : Set where
  requestSocketDeclared :
    SIConstantAuthorityEvidenceState
  externalEvidenceMissing :
    SIConstantAuthorityEvidenceState

data SIConstantAuthorityEvidenceDependency : Set where
  dependsOnArtifactRequest :
    SIConstantAuthorityEvidenceDependency
  dependsOnParsedCarrierRequest :
    SIConstantAuthorityEvidenceDependency
  dependsOnExternalImporter :
    SIConstantAuthorityEvidenceDependency
  dependsOnConsumerIngestion :
    SIConstantAuthorityEvidenceDependency

record SIConstantAuthorityEvidenceSocket : Set where
  field
    fieldKey :
      SIConstantAuthorityEvidenceField
    fieldName :
      String
    ownerSurface :
      String
    sourceRef :
      String
    dependency :
      SIConstantAuthorityEvidenceDependency
    evidenceState :
      SIConstantAuthorityEvidenceState
    socketDeclared :
      Bool
    socketDeclaredIsTrue :
      socketDeclared ≡ true
    evidenceAccepted :
      Bool
    evidenceAcceptedIsFalse :
      evidenceAccepted ≡ false
    promotesAuthority :
      Bool
    promotesAuthorityIsFalse :
      promotesAuthority ≡ false

open SIConstantAuthorityEvidenceSocket public

mkOpenEvidenceSocket :
  SIConstantAuthorityEvidenceField →
  String →
  String →
  String →
  SIConstantAuthorityEvidenceDependency →
  SIConstantAuthorityEvidenceSocket
mkOpenEvidenceSocket key name owner ref dependency =
  record
    { fieldKey =
        key
    ; fieldName =
        name
    ; ownerSurface =
        owner
    ; sourceRef =
        ref
    ; dependency =
        dependency
    ; evidenceState =
        externalEvidenceMissing
    ; socketDeclared =
        true
    ; socketDeclaredIsTrue =
        refl
    ; evidenceAccepted =
        false
    ; evidenceAcceptedIsFalse =
        refl
    ; promotesAuthority =
        false
    ; promotesAuthorityIsFalse =
        refl
    }

canonicalAuthorityArtifactIdentitySocket :
  SIConstantAuthorityEvidenceSocket
canonicalAuthorityArtifactIdentitySocket =
  mkOpenEvidenceSocket
    authorityArtifactIdentityField
    "authorityArtifact"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "SIArtifact.SIArtifactRequestFields.artifactIdentity"
    dependsOnExternalImporter

canonicalAuthorityArtifactSha256Socket :
  SIConstantAuthorityEvidenceSocket
canonicalAuthorityArtifactSha256Socket =
  mkOpenEvidenceSocket
    authorityArtifactSha256Field
    "authorityArtifactSha256"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "SIArtifact.SIArtifactRequestFields.artifactSha256"
    dependsOnExternalImporter

canonicalAuthorityAccessDateEvidenceSocket :
  SIConstantAuthorityEvidenceSocket
canonicalAuthorityAccessDateEvidenceSocket =
  mkOpenEvidenceSocket
    authorityAccessDateEvidenceField
    "authorityAccessDateEvidence"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "SIArtifact.SIArtifactRequestFields.artifactAccessDate"
    dependsOnExternalImporter

canonicalRawNumericTextSocket :
  SIConstantAuthorityEvidenceSocket
canonicalRawNumericTextSocket =
  mkOpenEvidenceSocket
    rawNumericTextField
    "rawNumericValueText"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "SIArtifact.rawValueText canonical*AuthorityArtifactRowRequest"
    dependsOnArtifactRequest

canonicalRawUncertaintyTextSocket :
  SIConstantAuthorityEvidenceSocket
canonicalRawUncertaintyTextSocket =
  mkOpenEvidenceSocket
    rawUncertaintyTextField
    "rawUncertaintyText"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "SIArtifact.exactZeroUncertaintyText"
    dependsOnArtifactRequest

canonicalParsedCarrierPayloadSocket :
  SIConstantAuthorityEvidenceSocket
canonicalParsedCarrierPayloadSocket =
  mkOpenEvidenceSocket
    parsedCarrierPayloadField
    "parsedNumericCarrierPayload"
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    "Parsed.SIExactParsedCarrierRowRequest"
    dependsOnParsedCarrierRequest

canonicalCovarianceOrIndependenceReceiptSocket :
  SIConstantAuthorityEvidenceSocket
canonicalCovarianceOrIndependenceReceiptSocket =
  mkOpenEvidenceSocket
    covarianceOrIndependenceReceiptField
    "covarianceMatrixOrIndependenceReceipt"
    "DASHI.Promotion.NumericAuthorityPayloadValidator"
    "Payload.missingCovarianceField"
    dependsOnExternalImporter

canonicalConsumerIngestionReceiptSocket :
  SIConstantAuthorityEvidenceSocket
canonicalConsumerIngestionReceiptSocket =
  mkOpenEvidenceSocket
    consumerIngestionReceiptField
    "consumerValueIngestionReceipt"
    "future SI consumer ingestion receipt"
    "Payload.missingConsumerIngestionReceiptField"
    dependsOnConsumerIngestion

canonicalSIConstantAuthorityEvidenceSockets :
  List SIConstantAuthorityEvidenceSocket
canonicalSIConstantAuthorityEvidenceSockets =
  canonicalAuthorityArtifactIdentitySocket
  ∷ canonicalAuthorityArtifactSha256Socket
  ∷ canonicalAuthorityAccessDateEvidenceSocket
  ∷ canonicalRawNumericTextSocket
  ∷ canonicalRawUncertaintyTextSocket
  ∷ canonicalParsedCarrierPayloadSocket
  ∷ canonicalCovarianceOrIndependenceReceiptSocket
  ∷ canonicalConsumerIngestionReceiptSocket
  ∷ []

data SIConstantEvidenceTarget : Set where
  deltaNuCsEvidenceTarget :
    SIConstantEvidenceTarget
  speedOfLightCEvidenceTarget :
    SIConstantEvidenceTarget
  planckConstantHEvidenceTarget :
    SIConstantEvidenceTarget

record SIConstantAuthorityEvidenceRow : Set₁ where
  field
    target :
      SIConstantEvidenceTarget
    rowLabel :
      String
    sourceRegistryRow :
      Registry.KnownConstantSlot
    sourceArtifactRow :
      SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest
    parsedCarrierRow :
      Parsed.SIExactParsedCarrierRowRequest
    artifactManifest :
      SIArtifact.SIDefiningConstantsAuthorityArtifactRequestManifest
    parsedCarrierManifest :
      Parsed.SIExactConstantParsedCarrierRequestManifest
    artifactRequestRef :
      String
    parsedCarrierRef :
      String
    registryRowRef :
      String
    rawNumericText :
      String
    rawNumericTextMatchesArtifactRequest :
      rawNumericText ≡ SIArtifact.rawValueText sourceArtifactRow
    rawUncertaintyText :
      String
    rawUncertaintyTextIsZero :
      rawUncertaintyText ≡ "0"
    unitText :
      String
    unitTextMatchesRegistryRow :
      unitText ≡ Registry.KnownConstantSlot.unit sourceRegistryRow
    evidenceSockets :
      List SIConstantAuthorityEvidenceSocket
    evidenceSocketCount :
      Nat
    evidenceSocketCountIs8 :
      evidenceSocketCount ≡ 8
    authorityArtifactIdentityAccepted :
      Bool
    authorityArtifactIdentityAcceptedIsFalse :
      authorityArtifactIdentityAccepted ≡ false
    authorityArtifactSha256Accepted :
      Bool
    authorityArtifactSha256AcceptedIsFalse :
      authorityArtifactSha256Accepted ≡ false
    authorityAccessDateEvidenceAccepted :
      Bool
    authorityAccessDateEvidenceAcceptedIsFalse :
      authorityAccessDateEvidenceAccepted ≡ false
    parsedCarrierPayloadAccepted :
      Bool
    parsedCarrierPayloadAcceptedIsFalse :
      parsedCarrierPayloadAccepted ≡ false
    covarianceOrIndependenceReceiptAccepted :
      Bool
    covarianceOrIndependenceReceiptAcceptedIsFalse :
      covarianceOrIndependenceReceiptAccepted ≡ false
    consumerIngestionReceiptAccepted :
      Bool
    consumerIngestionReceiptAcceptedIsFalse :
      consumerIngestionReceiptAccepted ≡ false
    rowAuthorityTokenAccepted :
      Bool
    rowAuthorityTokenAcceptedIsFalse :
      rowAuthorityTokenAccepted ≡ false
    rowPromoted :
      Bool
    rowPromotedIsFalse :
      rowPromoted ≡ false
    rowInheritsArtifactFailClosedGuard :
      SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest.rowPromoted
        sourceArtifactRow
      ≡
      rowPromoted
    rowInheritsParsedCarrierFailClosedGuard :
      Parsed.SIExactParsedCarrierRowRequest.numericValuePromoted
        parsedCarrierRow
      ≡
      rowPromoted

open SIConstantAuthorityEvidenceRow public

mkEvidenceRow :
  SIConstantEvidenceTarget →
  String →
  Registry.KnownConstantSlot →
  (artifactRow : SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest) →
  (parsedRow : Parsed.SIExactParsedCarrierRowRequest) →
  String →
  String →
  String →
  (rawText : String) →
  rawText ≡ SIArtifact.rawValueText artifactRow →
  SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest.rowPromoted
    artifactRow
  ≡
  false →
  Parsed.SIExactParsedCarrierRowRequest.numericValuePromoted
    parsedRow
  ≡
  false →
  SIConstantAuthorityEvidenceRow
mkEvidenceRow
  target label registryRow artifactRow parsedRow artifactRef parsedRef registryRef
  rawText rawTextMatches artifactRowPromotedIsFalse parsedRowPromotedIsFalse =
  record
    { target =
        target
    ; rowLabel =
        label
    ; sourceRegistryRow =
        registryRow
    ; sourceArtifactRow =
        artifactRow
    ; parsedCarrierRow =
        parsedRow
    ; artifactManifest =
        SIArtifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; parsedCarrierManifest =
        Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; artifactRequestRef =
        artifactRef
    ; parsedCarrierRef =
        parsedRef
    ; registryRowRef =
        registryRef
    ; rawNumericText =
        rawText
    ; rawNumericTextMatchesArtifactRequest =
        rawTextMatches
    ; rawUncertaintyText =
        SIArtifact.exactZeroUncertaintyText
    ; rawUncertaintyTextIsZero =
        refl
    ; unitText =
        Registry.KnownConstantSlot.unit registryRow
    ; unitTextMatchesRegistryRow =
        refl
    ; evidenceSockets =
        canonicalSIConstantAuthorityEvidenceSockets
    ; evidenceSocketCount =
        Payload.listCount canonicalSIConstantAuthorityEvidenceSockets
    ; evidenceSocketCountIs8 =
        refl
    ; authorityArtifactIdentityAccepted =
        false
    ; authorityArtifactIdentityAcceptedIsFalse =
        refl
    ; authorityArtifactSha256Accepted =
        false
    ; authorityArtifactSha256AcceptedIsFalse =
        refl
    ; authorityAccessDateEvidenceAccepted =
        false
    ; authorityAccessDateEvidenceAcceptedIsFalse =
        refl
    ; parsedCarrierPayloadAccepted =
        false
    ; parsedCarrierPayloadAcceptedIsFalse =
        refl
    ; covarianceOrIndependenceReceiptAccepted =
        false
    ; covarianceOrIndependenceReceiptAcceptedIsFalse =
        refl
    ; consumerIngestionReceiptAccepted =
        false
    ; consumerIngestionReceiptAcceptedIsFalse =
        refl
    ; rowAuthorityTokenAccepted =
        false
    ; rowAuthorityTokenAcceptedIsFalse =
        refl
    ; rowPromoted =
        false
    ; rowPromotedIsFalse =
        refl
    ; rowInheritsArtifactFailClosedGuard =
        artifactRowPromotedIsFalse
    ; rowInheritsParsedCarrierFailClosedGuard =
        parsedRowPromotedIsFalse
    }

canonicalDeltaNuCsAuthorityEvidenceRow :
  SIConstantAuthorityEvidenceRow
canonicalDeltaNuCsAuthorityEvidenceRow =
  mkEvidenceRow
    deltaNuCsEvidenceTarget
    "Delta nu Cs authority evidence checklist row"
    SIArtifact.canonicalDeltaNuCsRegistryRow
    SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest
    Parsed.canonicalDeltaNuCsParsedCarrierRowRequest
    "SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest"
    "Parsed.canonicalDeltaNuCsParsedCarrierRowRequest"
    SIArtifact.canonicalDeltaNuCsRegistrySourceRef
    (SIArtifact.rawValueText
      SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest)
    refl
    (SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest.rowPromotedIsFalse
      SIArtifact.canonicalDeltaNuCsAuthorityArtifactRowRequest)
    (Parsed.SIExactParsedCarrierRowRequest.numericValuePromotedIsFalse
      Parsed.canonicalDeltaNuCsParsedCarrierRowRequest)

canonicalCAuthorityEvidenceRow :
  SIConstantAuthorityEvidenceRow
canonicalCAuthorityEvidenceRow =
  mkEvidenceRow
    speedOfLightCEvidenceTarget
    "c authority evidence checklist row"
    SIArtifact.canonicalCRegistryRow
    SIArtifact.canonicalCAuthorityArtifactRowRequest
    Parsed.canonicalCParsedCarrierRowRequest
    "SIArtifact.canonicalCAuthorityArtifactRowRequest"
    "Parsed.canonicalCParsedCarrierRowRequest"
    SIArtifact.canonicalCRegistrySourceRef
    (SIArtifact.rawValueText
      SIArtifact.canonicalCAuthorityArtifactRowRequest)
    refl
    (SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest.rowPromotedIsFalse
      SIArtifact.canonicalCAuthorityArtifactRowRequest)
    (Parsed.SIExactParsedCarrierRowRequest.numericValuePromotedIsFalse
      Parsed.canonicalCParsedCarrierRowRequest)

canonicalHAuthorityEvidenceRow :
  SIConstantAuthorityEvidenceRow
canonicalHAuthorityEvidenceRow =
  mkEvidenceRow
    planckConstantHEvidenceTarget
    "h authority evidence checklist row"
    SIArtifact.canonicalHRegistryRow
    SIArtifact.canonicalHAuthorityArtifactRowRequest
    Parsed.canonicalHParsedCarrierRowRequest
    "SIArtifact.canonicalHAuthorityArtifactRowRequest"
    "Parsed.canonicalHParsedCarrierRowRequest"
    SIArtifact.canonicalHRegistrySourceRef
    (SIArtifact.rawValueText
      SIArtifact.canonicalHAuthorityArtifactRowRequest)
    refl
    (SIArtifact.SIDefiningConstantAuthorityArtifactRowRequest.rowPromotedIsFalse
      SIArtifact.canonicalHAuthorityArtifactRowRequest)
    (Parsed.SIExactParsedCarrierRowRequest.numericValuePromotedIsFalse
      Parsed.canonicalHParsedCarrierRowRequest)

record SIConstantAuthorityEvidenceChecklistManifest : Set₁ where
  field
    manifestLabel :
      String
    artifactManifest :
      SIArtifact.SIDefiningConstantsAuthorityArtifactRequestManifest
    parsedCarrierManifest :
      Parsed.SIExactConstantParsedCarrierRequestManifest
    evidenceRows :
      List SIConstantAuthorityEvidenceRow
    evidenceRowCount :
      Nat
    evidenceRowCountIs3 :
      evidenceRowCount ≡ 3
    evidenceSockets :
      List SIConstantAuthorityEvidenceSocket
    evidenceSocketCount :
      Nat
    evidenceSocketCountIs8 :
      evidenceSocketCount ≡ 8
    evidencePayloadSummary :
      List String
    evidencePayloadSummaryCount :
      Nat
    evidencePayloadSummaryCountIs8 :
      evidencePayloadSummaryCount ≡ 8
    exactConstantSummary :
      List String
    exactConstantSummaryCount :
      Nat
    exactConstantSummaryCountIs3 :
      exactConstantSummaryCount ≡ 3
    anyArtifactEvidenceAccepted :
      Bool
    anyArtifactEvidenceAcceptedIsFalse :
      anyArtifactEvidenceAccepted ≡ false
    allParsedCarrierPayloadsAccepted :
      Bool
    allParsedCarrierPayloadsAcceptedIsFalse :
      allParsedCarrierPayloadsAccepted ≡ false
    anyConsumerIngestionReceiptAccepted :
      Bool
    anyConsumerIngestionReceiptAcceptedIsFalse :
      anyConsumerIngestionReceiptAccepted ≡ false
    candidate256AuthorityTokenConstructed :
      Bool
    candidate256AuthorityTokenConstructedIsFalse :
      candidate256AuthorityTokenConstructed ≡ false
    anySIConstantPromoted :
      Bool
    anySIConstantPromotedIsFalse :
      anySIConstantPromoted ≡ false
    manifestInheritsArtifactFailClosedGuard :
      SIArtifact.SIDefiningConstantsAuthorityArtifactRequestManifest.anyRowPromoted
        artifactManifest
      ≡
      anySIConstantPromoted
    manifestInheritsParsedCarrierFailClosedGuard :
      Parsed.SIExactConstantParsedCarrierRequestManifest.anyNumericValuePromoted
        parsedCarrierManifest
      ≡
      anySIConstantPromoted

open SIConstantAuthorityEvidenceChecklistManifest public

canonicalSIConstantAuthorityEvidencePayloadSummary :
  List String
canonicalSIConstantAuthorityEvidencePayloadSummary =
  "authorityArtifact: external BIPM/NIST artifact identity still missing"
  ∷ "authorityArtifactSha256: external SHA-256 digest still missing"
  ∷ "authorityAccessDateEvidence: ISO access-date evidence still missing"
  ∷ "rawNumericValueText: request text is named but not artifact-verified"
  ∷ "rawUncertaintyText: exact zero-uncertainty request is named"
  ∷ "parsedNumericCarrierPayload: structural carrier exists but is not accepted"
  ∷ "covarianceMatrixOrIndependenceReceipt: independence receipt still missing"
  ∷ "consumerValueIngestionReceipt: consumer ingestion receipt still missing"
  ∷ []

canonicalSIConstantAuthorityEvidenceExactConstantSummary :
  List String
canonicalSIConstantAuthorityEvidenceExactConstantSummary =
  "Delta nu Cs -> SI second / atomic-clock carrier route"
  ∷ "c -> metre-from-second adapter and redshift denominator route"
  ∷ "h -> hbar expression and Stone/Schrodinger route"
  ∷ []

canonicalSIConstantAuthorityEvidenceChecklistManifest :
  SIConstantAuthorityEvidenceChecklistManifest
canonicalSIConstantAuthorityEvidenceChecklistManifest =
  record
    { manifestLabel =
        "Fail-closed SI defining-constant authority evidence checklist"
    ; artifactManifest =
        SIArtifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; parsedCarrierManifest =
        Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; evidenceRows =
        canonicalDeltaNuCsAuthorityEvidenceRow
        ∷ canonicalCAuthorityEvidenceRow
        ∷ canonicalHAuthorityEvidenceRow
        ∷ []
    ; evidenceRowCount =
        Payload.listCount
          ( canonicalDeltaNuCsAuthorityEvidenceRow
          ∷ canonicalCAuthorityEvidenceRow
          ∷ canonicalHAuthorityEvidenceRow
          ∷ []
          )
    ; evidenceRowCountIs3 =
        refl
    ; evidenceSockets =
        canonicalSIConstantAuthorityEvidenceSockets
    ; evidenceSocketCount =
        Payload.listCount canonicalSIConstantAuthorityEvidenceSockets
    ; evidenceSocketCountIs8 =
        refl
    ; evidencePayloadSummary =
        canonicalSIConstantAuthorityEvidencePayloadSummary
    ; evidencePayloadSummaryCount =
        Payload.listCount canonicalSIConstantAuthorityEvidencePayloadSummary
    ; evidencePayloadSummaryCountIs8 =
        refl
    ; exactConstantSummary =
        canonicalSIConstantAuthorityEvidenceExactConstantSummary
    ; exactConstantSummaryCount =
        Payload.listCount canonicalSIConstantAuthorityEvidenceExactConstantSummary
    ; exactConstantSummaryCountIs3 =
        refl
    ; anyArtifactEvidenceAccepted =
        false
    ; anyArtifactEvidenceAcceptedIsFalse =
        refl
    ; allParsedCarrierPayloadsAccepted =
        false
    ; allParsedCarrierPayloadsAcceptedIsFalse =
        refl
    ; anyConsumerIngestionReceiptAccepted =
        false
    ; anyConsumerIngestionReceiptAcceptedIsFalse =
        refl
    ; candidate256AuthorityTokenConstructed =
        false
    ; candidate256AuthorityTokenConstructedIsFalse =
        refl
    ; anySIConstantPromoted =
        false
    ; anySIConstantPromotedIsFalse =
        refl
    ; manifestInheritsArtifactFailClosedGuard =
        SIArtifact.SIDefiningConstantsAuthorityArtifactRequestManifest.anyRowPromotedIsFalse
          SIArtifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; manifestInheritsParsedCarrierFailClosedGuard =
        Parsed.SIExactConstantParsedCarrierRequestManifest.anyNumericValuePromotedIsFalse
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    }

siConstantAuthorityEvidenceChecklistRowCountIs3 :
  SIConstantAuthorityEvidenceChecklistManifest.evidenceRowCount
    canonicalSIConstantAuthorityEvidenceChecklistManifest
  ≡
  3
siConstantAuthorityEvidenceChecklistRowCountIs3 =
  refl

siConstantAuthorityEvidenceChecklistSocketCountIs8 :
  SIConstantAuthorityEvidenceChecklistManifest.evidenceSocketCount
    canonicalSIConstantAuthorityEvidenceChecklistManifest
  ≡
  8
siConstantAuthorityEvidenceChecklistSocketCountIs8 =
  refl

siConstantAuthorityEvidenceChecklistNoArtifactEvidence :
  SIConstantAuthorityEvidenceChecklistManifest.anyArtifactEvidenceAccepted
    canonicalSIConstantAuthorityEvidenceChecklistManifest
  ≡
  false
siConstantAuthorityEvidenceChecklistNoArtifactEvidence =
  refl

siConstantAuthorityEvidenceChecklistNoCandidate256Token :
  SIConstantAuthorityEvidenceChecklistManifest.candidate256AuthorityTokenConstructed
    canonicalSIConstantAuthorityEvidenceChecklistManifest
  ≡
  false
siConstantAuthorityEvidenceChecklistNoCandidate256Token =
  refl

siConstantAuthorityEvidenceChecklistNoPromotion :
  SIConstantAuthorityEvidenceChecklistManifest.anySIConstantPromoted
    canonicalSIConstantAuthorityEvidenceChecklistManifest
  ≡
  false
siConstantAuthorityEvidenceChecklistNoPromotion =
  refl
