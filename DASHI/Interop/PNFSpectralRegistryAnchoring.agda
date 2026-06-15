module DASHI.Interop.PNFSpectralRegistryAnchoring where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFSpectralVectorIndex as Vector

------------------------------------------------------------------------
-- PNF evidence anchoring and object-registry invariants.
--
-- This module is a checked receipt surface only.  It gives names to
-- canonical document references, evidence spans, version/profile hashes,
-- registry rows, identity authority, resolver preconditions, and the
-- fail-closed booleans that keep unanchored or stale runtime material out of
-- the admitted object lane.

data PNFSpectralRegistryAnchoringStatus : Set where
  checkedRegistryAnchoringSurface_failClosed :
    PNFSpectralRegistryAnchoringStatus

------------------------------------------------------------------------
-- Sections 1 and 2: canonical documents and evidence spans.

data DocumentRefKind : Set where
  statuteDocument : DocumentRefKind
  regulationDocument : DocumentRefKind
  caseDocument : DocumentRefKind
  transcriptDocument : DocumentRefKind
  corpusDocument : DocumentRefKind
  syntheticFixtureDocument : DocumentRefKind

record CanonicalDocumentRef : Set where
  constructor canonicalDocumentRef
  field
    documentKind : DocumentRefKind
    documentNamespace : String
    documentIdentifier : String
    documentCanonicalURI : String
    documentAuthorityProfile : String

open CanonicalDocumentRef public

data EvidenceSpanSelector : Set where
  byteOffsets : EvidenceSpanSelector
  characterOffsets : EvidenceSpanSelector
  paragraphOrdinal : EvidenceSpanSelector
  clauseOrdinal : EvidenceSpanSelector
  wholeDocumentSpan : EvidenceSpanSelector

record EvidenceSpanRef : Set where
  constructor evidenceSpanRef
  field
    spanDocument : CanonicalDocumentRef
    spanSelector : EvidenceSpanSelector
    spanStart : Nat
    spanEnd : Nat
    spanTextDigest : String
    spanAnchoredToCanonicalDocument : Bool

open EvidenceSpanRef public

------------------------------------------------------------------------
-- Sections 6 and 13: version hashes, parser/reducer profiles, and payloads.

data HashAlgorithm : Set where
  sha256 : HashAlgorithm
  blake3 : HashAlgorithm
  fixtureHashAlgorithm : HashAlgorithm

record VersionHash : Set where
  constructor versionHash
  field
    hashAlgorithm : HashAlgorithm
    hashValue : String
    versionProfile : String
    hashBindsCanonicalDocument : Bool
    hashBindsStructuralPayload : Bool

open VersionHash public

record ParserReducerProfile : Set where
  constructor parserReducerProfile
  field
    parserProfile : String
    reducerProfile : String
    parserProfileHash : VersionHash
    reducerProfileHash : VersionHash
    profileDeclaredByReceipt : Bool
    runtimeParserHasAuthority : Bool

open ParserReducerProfile public

record StructuralPayloadAnchor : Set where
  constructor structuralPayloadAnchor
  field
    payloadObject : Core.PredicateObjectRef
    payloadSignature : Residual.StructuralSignature
    payloadQualifier : Residual.QualifierState
    payloadWrapper : Residual.WrapperState
    structuralHash : String
    payloadHash : String
    payloadHashProfile : VersionHash
    payloadBindsObject : Bool
    payloadBindsSpan : Bool

open StructuralPayloadAnchor public

------------------------------------------------------------------------
-- Sections 13 and 15: registry rows, identity authority, and gates.

data RegistryRowStatus : Set where
  rowRegistered : RegistryRowStatus
  rowRejectedFailClosed : RegistryRowStatus

record ObjectRegistryRow : Set where
  constructor objectRegistryRow
  field
    rowObject : Vector.ObjectRef
    rowDocument : CanonicalDocumentRef
    rowSpan : EvidenceSpanRef
    rowVersionHash : VersionHash
    rowParserReducerProfile : ParserReducerProfile
    rowStructuralPayload : StructuralPayloadAnchor
    rowRegistryHash : String
    rowStatus : RegistryRowStatus
    rowAnchoredObject : Bool
    rowHasReceipt : Bool
    rowCurrentVersion : Bool
    rowAdmitsVectorRowAuthority : Bool
    rowAdmitsRuntimeParserAuthority : Bool

open ObjectRegistryRow public

data RegistryIdentityAuthorityKind : Set where
  canonicalRegistryAuthorityKind : RegistryIdentityAuthorityKind
  fixtureRegistryAuthority : RegistryIdentityAuthorityKind

record RegistryIdentityAuthority : Set where
  constructor registryIdentityAuthority
  field
    authorityKind : RegistryIdentityAuthorityKind
    authorityName : String
    authorityProfile : String
    authorityVersionHash : VersionHash
    authorityControlsObjectIdentity : Bool
    authorityAcceptsVectorRowIdentity : Bool
    authorityAcceptsRuntimeParserIdentity : Bool

open RegistryIdentityAuthority public

record ResolverPreconditions : Set where
  constructor resolverPreconditions
  field
    resolverCandidate : Vector.CandidateRef
    resolverRegistryRow : ObjectRegistryRow
    resolverIdentityAuthority : RegistryIdentityAuthority
    requiresAnchoredObject : Bool
    requiresCurrentVersion : Bool
    requiresReceipt : Bool
    rejectsVectorRowAuthority : Bool
    rejectsRuntimeParserAuthority : Bool
    resolverMayProceed : Bool

open ResolverPreconditions public

record FailClosedAdmissionGates : Set where
  constructor failClosedAdmissionGates
  field
    unanchoredObjectAdmission : Bool
    vectorRowAuthorityAdmission : Bool
    staleVersionAdmission : Bool
    missingReceiptAdmission : Bool
    runtimeParserAuthorityAdmission : Bool

open FailClosedAdmissionGates public

canonicalFailClosedAdmissionGates : FailClosedAdmissionGates
canonicalFailClosedAdmissionGates =
  failClosedAdmissionGates
    false
    false
    false
    false
    false

canonicalUnanchoredObjectAdmissionFailsClosed :
  unanchoredObjectAdmission canonicalFailClosedAdmissionGates ≡ false
canonicalUnanchoredObjectAdmissionFailsClosed =
  refl

canonicalVectorRowAuthorityAdmissionFailsClosed :
  vectorRowAuthorityAdmission canonicalFailClosedAdmissionGates ≡ false
canonicalVectorRowAuthorityAdmissionFailsClosed =
  refl

canonicalStaleVersionAdmissionFailsClosed :
  staleVersionAdmission canonicalFailClosedAdmissionGates ≡ false
canonicalStaleVersionAdmissionFailsClosed =
  refl

canonicalMissingReceiptAdmissionFailsClosed :
  missingReceiptAdmission canonicalFailClosedAdmissionGates ≡ false
canonicalMissingReceiptAdmissionFailsClosed =
  refl

canonicalRuntimeParserAuthorityAdmissionFailsClosed :
  runtimeParserAuthorityAdmission canonicalFailClosedAdmissionGates ≡ false
canonicalRuntimeParserAuthorityAdmissionFailsClosed =
  refl

------------------------------------------------------------------------
-- Canonical example receipt.

canonicalDocument : CanonicalDocumentRef
canonicalDocument =
  canonicalDocumentRef
    syntheticFixtureDocument
    "dashi/pnf/fixture"
    "registry-anchoring-example"
    "urn:dashi:pnf:fixture:registry-anchoring-example"
    "canonical-document-ref-v1"

canonicalEvidenceSpan : EvidenceSpanRef
canonicalEvidenceSpan =
  evidenceSpanRef
    canonicalDocument
    characterOffsets
    zero
    (suc (suc (suc (suc (suc zero)))))
    "span-digest-fixture"
    true

canonicalVersionHash : VersionHash
canonicalVersionHash =
  versionHash
    sha256
    "sha256:canonical-document-version-fixture"
    "document-version-hash-v1"
    true
    true

canonicalParserHash : VersionHash
canonicalParserHash =
  versionHash
    sha256
    "sha256:canonical-parser-profile-fixture"
    "parser-profile-hash-v1"
    true
    false

canonicalReducerHash : VersionHash
canonicalReducerHash =
  versionHash
    sha256
    "sha256:canonical-reducer-profile-fixture"
    "reducer-profile-hash-v1"
    true
    false

canonicalParserReducerProfile : ParserReducerProfile
canonicalParserReducerProfile =
  parserReducerProfile
    "pnf-parser-profile-v1"
    "pnf-reducer-profile-v1"
    canonicalParserHash
    canonicalReducerHash
    true
    false

canonicalStructuralPayloadAnchor : StructuralPayloadAnchor
canonicalStructuralPayloadAnchor =
  structuralPayloadAnchor
    Core.canonicalPredicateObjectRef
    Residual.sig-agent-theme
    Residual.positive
    Residual.directEvidence
    "structural-hash-fixture"
    "payload-hash-fixture"
    canonicalVersionHash
    true
    true

canonicalRegistryObject : Vector.ObjectRef
canonicalRegistryObject =
  Vector.objectRef
    Core.canonicalPredicateObjectRef
    "anchored-pnf-object"

canonicalRegistryRow : ObjectRegistryRow
canonicalRegistryRow =
  objectRegistryRow
    canonicalRegistryObject
    canonicalDocument
    canonicalEvidenceSpan
    canonicalVersionHash
    canonicalParserReducerProfile
    canonicalStructuralPayloadAnchor
    "registry-row-hash-fixture"
    rowRegistered
    true
    true
    true
    false
    false

canonicalRegistryAuthority : RegistryIdentityAuthority
canonicalRegistryAuthority =
  registryIdentityAuthority
    canonicalRegistryAuthorityKind
    "pnf-object-registry"
    "registry-identity-authority-v1"
    canonicalVersionHash
    true
    false
    false

canonicalVectorCoordinate : Vector.VectorCoordinate
canonicalVectorCoordinate =
  Vector.vectorCoordinate zero "registry-anchoring-coordinate"

canonicalVectorRow : Vector.VectorIndexRow
canonicalVectorRow =
  Vector.vectorIndexRow
    Vector.pnfSpectralLaplacianV1
    canonicalVectorCoordinate
    canonicalRegistryObject
    true
    false
    false
    false

canonicalCandidate : Vector.CandidateRef
canonicalCandidate =
  Vector.rowToCandidateRef zero canonicalVectorRow

canonicalResolverPreconditions : ResolverPreconditions
canonicalResolverPreconditions =
  resolverPreconditions
    canonicalCandidate
    canonicalRegistryRow
    canonicalRegistryAuthority
    true
    true
    true
    true
    true
    true

record PNFSpectralRegistryAnchoringReceipt : Set where
  constructor pnfSpectralRegistryAnchoringReceipt
  field
    receiptDocument : CanonicalDocumentRef
    receiptDocumentIsCanonical :
      receiptDocument ≡ canonicalDocument

    receiptEvidenceSpan : EvidenceSpanRef
    receiptSpanDocumentIsReceiptDocument :
      spanDocument receiptEvidenceSpan ≡ receiptDocument
    receiptSpanAnchored :
      spanAnchoredToCanonicalDocument receiptEvidenceSpan ≡ true

    receiptVersionHash : VersionHash
    receiptHashBindsDocument :
      hashBindsCanonicalDocument receiptVersionHash ≡ true
    receiptHashBindsPayload :
      hashBindsStructuralPayload receiptVersionHash ≡ true

    receiptParserReducerProfile : ParserReducerProfile
    receiptParserProfileDeclared :
      profileDeclaredByReceipt receiptParserReducerProfile ≡ true
    receiptRuntimeParserAuthorityIsFalse :
      runtimeParserHasAuthority receiptParserReducerProfile ≡ false

    receiptStructuralPayload : StructuralPayloadAnchor
    receiptPayloadBindsObject :
      payloadBindsObject receiptStructuralPayload ≡ true
    receiptPayloadBindsSpan :
      payloadBindsSpan receiptStructuralPayload ≡ true

    receiptRegistryObject : Vector.ObjectRef
    receiptRegistryRow : ObjectRegistryRow
    receiptRowObjectIsReceiptObject :
      rowObject receiptRegistryRow ≡ receiptRegistryObject
    receiptRowDocumentIsReceiptDocument :
      rowDocument receiptRegistryRow ≡ receiptDocument
    receiptRowSpanIsReceiptSpan :
      rowSpan receiptRegistryRow ≡ receiptEvidenceSpan
    receiptRowVersionIsReceiptVersion :
      rowVersionHash receiptRegistryRow ≡ receiptVersionHash
    receiptRowProfileIsReceiptProfile :
      rowParserReducerProfile receiptRegistryRow ≡ receiptParserReducerProfile
    receiptRowPayloadIsReceiptPayload :
      rowStructuralPayload receiptRegistryRow ≡ receiptStructuralPayload
    receiptRowAnchoredObject :
      rowAnchoredObject receiptRegistryRow ≡ true
    receiptRowHasReceipt :
      rowHasReceipt receiptRegistryRow ≡ true
    receiptRowCurrentVersion :
      rowCurrentVersion receiptRegistryRow ≡ true
    receiptRowVectorAuthorityIsFalse :
      rowAdmitsVectorRowAuthority receiptRegistryRow ≡ false
    receiptRowRuntimeParserAuthorityIsFalse :
      rowAdmitsRuntimeParserAuthority receiptRegistryRow ≡ false

    receiptIdentityAuthority : RegistryIdentityAuthority
    receiptAuthorityControlsIdentity :
      authorityControlsObjectIdentity receiptIdentityAuthority ≡ true
    receiptAuthorityRejectsVectorIdentity :
      authorityAcceptsVectorRowIdentity receiptIdentityAuthority ≡ false
    receiptAuthorityRejectsRuntimeParserIdentity :
      authorityAcceptsRuntimeParserIdentity receiptIdentityAuthority ≡ false

    receiptResolverPreconditions : ResolverPreconditions
    receiptResolverRowIsReceiptRow :
      resolverRegistryRow receiptResolverPreconditions ≡ receiptRegistryRow
    receiptResolverAuthorityIsReceiptAuthority :
      resolverIdentityAuthority receiptResolverPreconditions ≡ receiptIdentityAuthority
    receiptRequiresAnchoredObject :
      requiresAnchoredObject receiptResolverPreconditions ≡ true
    receiptRequiresCurrentVersion :
      requiresCurrentVersion receiptResolverPreconditions ≡ true
    receiptRequiresReceipt :
      requiresReceipt receiptResolverPreconditions ≡ true
    receiptRejectsVectorAuthority :
      rejectsVectorRowAuthority receiptResolverPreconditions ≡ true
    receiptRejectsRuntimeParserAuthority :
      rejectsRuntimeParserAuthority receiptResolverPreconditions ≡ true
    receiptResolverMayProceed :
      resolverMayProceed receiptResolverPreconditions ≡ true

    receiptFailClosedGates : FailClosedAdmissionGates
    receiptUnanchoredObjectAdmissionFailsClosed :
      unanchoredObjectAdmission receiptFailClosedGates ≡ false
    receiptVectorRowAuthorityAdmissionFailsClosed :
      vectorRowAuthorityAdmission receiptFailClosedGates ≡ false
    receiptStaleVersionAdmissionFailsClosed :
      staleVersionAdmission receiptFailClosedGates ≡ false
    receiptMissingReceiptAdmissionFailsClosed :
      missingReceiptAdmission receiptFailClosedGates ≡ false
    receiptRuntimeParserAuthorityAdmissionFailsClosed :
      runtimeParserAuthorityAdmission receiptFailClosedGates ≡ false

open PNFSpectralRegistryAnchoringReceipt public

canonicalPNFSpectralRegistryAnchoringReceipt :
  PNFSpectralRegistryAnchoringReceipt
canonicalPNFSpectralRegistryAnchoringReceipt =
  pnfSpectralRegistryAnchoringReceipt
    canonicalDocument
    refl
    canonicalEvidenceSpan
    refl
    refl
    canonicalVersionHash
    refl
    refl
    canonicalParserReducerProfile
    refl
    refl
    canonicalStructuralPayloadAnchor
    refl
    refl
    canonicalRegistryObject
    canonicalRegistryRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalRegistryAuthority
    refl
    refl
    refl
    canonicalResolverPreconditions
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalFailClosedAdmissionGates
    refl
    refl
    refl
    refl
    refl

canonicalReceipt : PNFSpectralRegistryAnchoringReceipt
canonicalReceipt =
  canonicalPNFSpectralRegistryAnchoringReceipt

canonicalReceiptDocumentRef :
  receiptDocument canonicalReceipt ≡ canonicalDocument
canonicalReceiptDocumentRef =
  refl

canonicalReceiptSpanAnchored :
  spanAnchoredToCanonicalDocument (receiptEvidenceSpan canonicalReceipt) ≡ true
canonicalReceiptSpanAnchored =
  refl

canonicalReceiptRuntimeParserAuthorityFalse :
  runtimeParserHasAuthority
    (receiptParserReducerProfile canonicalReceipt)
  ≡
  false
canonicalReceiptRuntimeParserAuthorityFalse =
  refl

canonicalReceiptRowVectorAuthorityFalse :
  rowAdmitsVectorRowAuthority (receiptRegistryRow canonicalReceipt) ≡ false
canonicalReceiptRowVectorAuthorityFalse =
  refl

canonicalReceiptRowCurrentVersion :
  rowCurrentVersion (receiptRegistryRow canonicalReceipt) ≡ true
canonicalReceiptRowCurrentVersion =
  refl

canonicalReceiptResolverRequiresReceipt :
  requiresReceipt (receiptResolverPreconditions canonicalReceipt) ≡ true
canonicalReceiptResolverRequiresReceipt =
  refl

canonicalReceiptMissingReceiptFailsClosed :
  missingReceiptAdmission (receiptFailClosedGates canonicalReceipt) ≡ false
canonicalReceiptMissingReceiptFailsClosed =
  refl

canonicalReceiptStaleVersionFailsClosed :
  staleVersionAdmission (receiptFailClosedGates canonicalReceipt) ≡ false
canonicalReceiptStaleVersionFailsClosed =
  refl
