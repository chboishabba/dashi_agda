module DASHI.Interop.PNFBraidTransportField where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFSpectralFieldCore as Spectral
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF braid transport field.
--
-- This module records temporal/source braid navigation for PNF field
-- candidates.  It is a transport/receipt surface only: a source event may
-- propose candidate refs through a braid path, but commit requires explicit
-- resolution, selection, and ITIR validation receipts.  No truth, source
-- authority, legal/policy authority, Wikidata authority, runtime ITIR
-- authority, physics theorem, or Clay promotion is constructed here.

data PNFBraidTransportStatus : Set where
  pnfBraidTransportRecordedNoPromotion :
    PNFBraidTransportStatus

data SourceEventKind : Set where
  newsEvent :
    SourceEventKind

  correctionEvent :
    SourceEventKind

  sourceUpdateEvent :
    SourceEventKind

  retractionEvent :
    SourceEventKind

  backgroundContextEvent :
    SourceEventKind

record SourceEvent : Set where
  constructor sourceEvent
  field
    eventKind :
      SourceEventKind

    sourceId :
      String

    sourceUrl :
      String

    sourceTitle :
      String

    sourceTimestamp :
      String

    sourceProvenance :
      String

open SourceEvent public

data TimeSliceKind : Set where
  initialSlice :
    TimeSliceKind

  revisionSlice :
    TimeSliceKind

  correctionSlice :
    TimeSliceKind

  supersededSlice :
    TimeSliceKind

record TimeSliceRevision : Set where
  constructor timeSliceRevision
  field
    sliceKind :
      TimeSliceKind

    revisionNumber :
      Nat

    observedAt :
      String

    revisionLabel :
      String

open TimeSliceRevision public

data PNFStrandRole : Set where
  sourceStrand :
    PNFStrandRole

  temporalStrand :
    PNFStrandRole

  candidateRefStrand :
    PNFStrandRole

  residualStrand :
    PNFStrandRole

  supportStrand :
    PNFStrandRole

record PNFRef : Set where
  constructor pnfRef
  field
    candidateRef :
      Residual.CandidateRef

    refLabel :
      String

    refProvenance :
      String

open PNFRef public

record PNFFibre : Set where
  constructor pnfFibre
  field
    fibreSignature :
      Residual.StructuralSignature

    fibreWrapper :
      Residual.WrapperState

    fibreQualifier :
      Residual.QualifierState

    fibreLabel :
      String

open PNFFibre public

record PNFStrand : Set where
  constructor pnfStrand
  field
    strandRole :
      PNFStrandRole

    strandRef :
      PNFRef

    strandFibre :
      PNFFibre

    strandSourceEvent :
      SourceEvent

    strandTimeSlice :
      TimeSliceRevision

open PNFStrand public

data PNFCrossingKind : Set where
  sameFibreCrossing :
    PNFCrossingKind

  partialResidualCrossing :
    PNFCrossingKind

  contradictionCrossing :
    PNFCrossingKind

  supportStrengthening :
    PNFCrossingKind

  supportWeakening :
    PNFCrossingKind

  sourceContinuation :
    PNFCrossingKind

canonicalCrossingKinds :
  List PNFCrossingKind
canonicalCrossingKinds =
  sameFibreCrossing
  ∷ partialResidualCrossing
  ∷ contradictionCrossing
  ∷ supportStrengthening
  ∷ supportWeakening
  ∷ sourceContinuation
  ∷ []

record PNFCrossing : Set where
  constructor pnfCrossing
  field
    crossingKind :
      PNFCrossingKind

    fromStrand :
      PNFStrand

    toStrand :
      PNFStrand

    residualLevel :
      Residual.ResidualLevel

    crossingReceiptId :
      String

    crossingIsTransportOnly :
      Bool

    crossingIsTransportOnlyIsTrue :
      crossingIsTransportOnly ≡ true

open PNFCrossing public

record BraidPath : Set where
  constructor braidPath
  field
    pathSourceEvent :
      SourceEvent

    pathInitialSlice :
      TimeSliceRevision

    pathTerminalSlice :
      TimeSliceRevision

    pathStrands :
      List PNFStrand

    pathCrossings :
      List PNFCrossing

    pathReceiptId :
      String

    pathIsNavigation :
      Bool

    pathIsNavigationIsTrue :
      pathIsNavigation ≡ true

open BraidPath public

record BraidSignature : Set where
  constructor braidSignature
  field
    signatureSource :
      SourceEvent

    signatureSlices :
      List TimeSliceRevision

    signatureCrossingKinds :
      List PNFCrossingKind

    signatureCandidateRefs :
      List PNFRef

    signatureFibres :
      List PNFFibre

    signatureReceiptId :
      String

    signatureIsBookkeeping :
      Bool

    signatureIsBookkeepingIsTrue :
      signatureIsBookkeeping ≡ true

open BraidSignature public

data TransportResolutionState : Set where
  proposedOnly :
    TransportResolutionState

  resolvedByConsumer :
    TransportResolutionState

  selectedByPolicy :
    TransportResolutionState

  itirValidated :
    TransportResolutionState

  commitReady :
    TransportResolutionState

data TransportCommitGate : Set where
  requiresResolution :
    TransportCommitGate

  requiresSelection :
    TransportCommitGate

  requiresITIRValidation :
    TransportCommitGate

  commitBlockedUntilReceipts :
    TransportCommitGate

canonicalNewsEventCommitGates :
  List TransportCommitGate
canonicalNewsEventCommitGates =
  requiresResolution
  ∷ requiresSelection
  ∷ requiresITIRValidation
  ∷ commitBlockedUntilReceipts
  ∷ []

record PNFTransportReceipt : Set where
  constructor pnfTransportReceipt
  field
    transportSource :
      PNFRef

    transportTarget :
      PNFRef

    sourceFibre :
      PNFFibre

    targetFibre :
      PNFFibre

    transportPath :
      BraidPath

    transportSignature :
      BraidSignature

    resolutionState :
      TransportResolutionState

    transportReceiptId :
      String

    transportIsReceiptRelation :
      Bool

    transportIsReceiptRelationIsTrue :
      transportIsReceiptRelation ≡ true

    transportAssertsTruth :
      Bool

    transportAssertsTruthIsFalse :
      transportAssertsTruth ≡ false

open PNFTransportReceipt public

record PNFTransportRelation (source target : PNFRef) : Set where
  constructor pnfTransportRelation
  field
    relationReceipt :
      PNFTransportReceipt

    relationSourceMatches :
      transportSource relationReceipt ≡ source

    relationTargetMatches :
      transportTarget relationReceipt ≡ target

    relationSourceFibre :
      PNFFibre

    relationTargetFibre :
      PNFFibre

    relationIsReceiptBearing :
      Bool

    relationIsReceiptBearingIsTrue :
      relationIsReceiptBearing ≡ true

    relationAssertsTruth :
      Bool

    relationAssertsTruthIsFalse :
      relationAssertsTruth ≡ false

open PNFTransportRelation public

_⇝pnf_ : PNFRef → PNFRef → Set
source ⇝pnf target =
  PNFTransportRelation source target

data PNFBraidTransportPromotion : Set where

pnfBraidTransportPromotionImpossible :
  PNFBraidTransportPromotion →
  ⊥
pnfBraidTransportPromotionImpossible ()

data PNFBraidTransportNonClaim : Set where
  noTruthClaim :
    PNFBraidTransportNonClaim

  noSourceAuthorityPromotion :
    PNFBraidTransportNonClaim

  noLegalOrPolicyAuthority :
    PNFBraidTransportNonClaim

  noWikidataAuthority :
    PNFBraidTransportNonClaim

  noRuntimeITIRAuthority :
    PNFBraidTransportNonClaim

  noCommitWithoutResolutionSelectionValidation :
    PNFBraidTransportNonClaim

  noPhysicsPromotion :
    PNFBraidTransportNonClaim

  noClayPromotion :
    PNFBraidTransportNonClaim

canonicalPNFBraidTransportNonClaims :
  List PNFBraidTransportNonClaim
canonicalPNFBraidTransportNonClaims =
  noTruthClaim
  ∷ noSourceAuthorityPromotion
  ∷ noLegalOrPolicyAuthority
  ∷ noWikidataAuthority
  ∷ noRuntimeITIRAuthority
  ∷ noCommitWithoutResolutionSelectionValidation
  ∷ noPhysicsPromotion
  ∷ noClayPromotion
  ∷ []

newsBraidCandidateStatement :
  String
newsBraidCandidateStatement =
  "A news source event braid may propose PNF candidate refs across temporal/source strands, but the candidates remain proposed-only until resolved, selected, and ITIR-validated by external receipts."

transportBoundaryStatement :
  String
transportBoundaryStatement =
  "PNF braid transport is a receipt-bearing navigation relation over refs and fibres; it is not semantic truth, source authority, policy authority, Wikidata authority, or runtime ITIR validation."

canonicalNewsSourceEvent :
  SourceEvent
canonicalNewsSourceEvent =
  sourceEvent
    newsEvent
    "source:news:event"
    "uncommitted-news-url"
    "uncommitted news event"
    "unvalidated-source-time"
    "source event provenance placeholder"

canonicalInitialSlice :
  TimeSliceRevision
canonicalInitialSlice =
  timeSliceRevision
    initialSlice
    0
    "observed-at-initial"
    "initial source event slice"

canonicalRevisionSlice :
  TimeSliceRevision
canonicalRevisionSlice =
  timeSliceRevision
    revisionSlice
    1
    "observed-at-revision"
    "candidate revision slice"

canonicalSourceRef :
  PNFRef
canonicalSourceRef =
  pnfRef
    (Residual.pnf-ref 0)
    "source event candidate ref"
    "candidate proposed from source event braid"

canonicalTargetRef :
  PNFRef
canonicalTargetRef =
  pnfRef
    (Residual.pnf-ref 1)
    "target candidate ref"
    "candidate requires resolution selection ITIR validation"

canonicalFallbackRef :
  PNFRef
canonicalFallbackRef =
  pnfRef
    Residual.pnf-fallback
    "fallback candidate ref"
    "fallback candidate remains uncommitted"

canonicalSourceFibre :
  PNFFibre
canonicalSourceFibre =
  pnfFibre
    Residual.sig-agent-theme
    Residual.attributedEvidence
    Residual.modal
    "attributed modal agent-theme source fibre"

canonicalTargetFibre :
  PNFFibre
canonicalTargetFibre =
  pnfFibre
    Residual.sig-agent-theme
    Residual.attributedEvidence
    Residual.modal
    "same-fibre target candidate"

canonicalFallbackFibre :
  PNFFibre
canonicalFallbackFibre =
  pnfFibre
    Residual.sig-unclassified
    Residual.wrapperUnknown
    Residual.qualifierUnknown
    "fallback unclassified fibre"

canonicalSourceStrand :
  PNFStrand
canonicalSourceStrand =
  pnfStrand
    sourceStrand
    canonicalSourceRef
    canonicalSourceFibre
    canonicalNewsSourceEvent
    canonicalInitialSlice

canonicalCandidateStrand :
  PNFStrand
canonicalCandidateStrand =
  pnfStrand
    candidateRefStrand
    canonicalTargetRef
    canonicalTargetFibre
    canonicalNewsSourceEvent
    canonicalRevisionSlice

canonicalResidualStrand :
  PNFStrand
canonicalResidualStrand =
  pnfStrand
    residualStrand
    canonicalFallbackRef
    canonicalFallbackFibre
    canonicalNewsSourceEvent
    canonicalRevisionSlice

canonicalSameFibreCrossing :
  PNFCrossing
canonicalSameFibreCrossing =
  pnfCrossing
    sameFibreCrossing
    canonicalSourceStrand
    canonicalCandidateStrand
    Residual.exact
    "crossing:same-fibre:receipt"
    true
    refl

canonicalPartialResidualCrossing :
  PNFCrossing
canonicalPartialResidualCrossing =
  pnfCrossing
    partialResidualCrossing
    canonicalCandidateStrand
    canonicalResidualStrand
    Residual.partial
    "crossing:partial-residual:receipt"
    true
    refl

canonicalNewsBraidPath :
  BraidPath
canonicalNewsBraidPath =
  braidPath
    canonicalNewsSourceEvent
    canonicalInitialSlice
    canonicalRevisionSlice
    (canonicalSourceStrand
      ∷ canonicalCandidateStrand
      ∷ canonicalResidualStrand
      ∷ [])
    (canonicalSameFibreCrossing
      ∷ canonicalPartialResidualCrossing
      ∷ [])
    "path:news-event-braid:candidate-navigation"
    true
    refl

canonicalNewsBraidSignature :
  BraidSignature
canonicalNewsBraidSignature =
  braidSignature
    canonicalNewsSourceEvent
    (canonicalInitialSlice ∷ canonicalRevisionSlice ∷ [])
    canonicalCrossingKinds
    (canonicalSourceRef ∷ canonicalTargetRef ∷ canonicalFallbackRef ∷ [])
    (canonicalSourceFibre ∷ canonicalTargetFibre ∷ canonicalFallbackFibre ∷ [])
    "signature:news-event-braid:candidates"
    true
    refl

canonicalNewsEventTransportReceipt :
  PNFTransportReceipt
canonicalNewsEventTransportReceipt =
  pnfTransportReceipt
    canonicalSourceRef
    canonicalTargetRef
    canonicalSourceFibre
    canonicalTargetFibre
    canonicalNewsBraidPath
    canonicalNewsBraidSignature
    proposedOnly
    "transport:news-event:candidate-only"
    true
    refl
    false
    refl

canonicalNewsEventTransportRelation :
  canonicalSourceRef ⇝pnf canonicalTargetRef
canonicalNewsEventTransportRelation =
  pnfTransportRelation
    canonicalNewsEventTransportReceipt
    refl
    refl
    canonicalSourceFibre
    canonicalTargetFibre
    true
    refl
    false
    refl

record PNFBraidTransportFieldReceipt : Set where
  field
    status :
      PNFBraidTransportStatus

    statusIsCanonical :
      status ≡ pnfBraidTransportRecordedNoPromotion

    importedSpectralCoreAcknowledged :
      Bool

    importedSpectralCoreAcknowledgedIsTrue :
      importedSpectralCoreAcknowledged ≡ true

    braidSourceEvent :
      SourceEvent

    braidSourceEventIsCanonical :
      braidSourceEvent ≡ canonicalNewsSourceEvent

    receiptInitialSlice :
      TimeSliceRevision

    receiptInitialSliceIsCanonical :
      receiptInitialSlice ≡ canonicalInitialSlice

    receiptRevisionSlice :
      TimeSliceRevision

    receiptRevisionSliceIsCanonical :
      receiptRevisionSlice ≡ canonicalRevisionSlice

    crossingKinds :
      List PNFCrossingKind

    crossingKindsAreCanonical :
      crossingKinds ≡ canonicalCrossingKinds

    candidateRefs :
      List PNFRef

    candidateRefsAreCanonical :
      candidateRefs
      ≡
      (canonicalSourceRef ∷ canonicalTargetRef ∷ canonicalFallbackRef ∷ [])

    fibres :
      List PNFFibre

    fibresAreCanonical :
      fibres
      ≡
      (canonicalSourceFibre ∷ canonicalTargetFibre ∷ canonicalFallbackFibre ∷ [])

    braidPathReceipt :
      BraidPath

    braidPathReceiptIsCanonical :
      braidPathReceipt ≡ canonicalNewsBraidPath

    braidSignatureReceipt :
      BraidSignature

    braidSignatureReceiptIsCanonical :
      braidSignatureReceipt ≡ canonicalNewsBraidSignature

    transportReceipt :
      PNFTransportReceipt

    transportReceiptIsCanonical :
      transportReceipt ≡ canonicalNewsEventTransportReceipt

    transportRelation :
      canonicalSourceRef ⇝pnf canonicalTargetRef

    transportRelationIsCanonical :
      transportRelation ≡ canonicalNewsEventTransportRelation

    transportRelationIsReceiptBearing :
      Bool

    transportRelationIsReceiptBearingIsTrue :
      transportRelationIsReceiptBearing ≡ true

    transportRelationAssertsTruth :
      Bool

    transportRelationAssertsTruthIsFalse :
      transportRelationAssertsTruth ≡ false

    newsBraidCanProposeCandidateRefs :
      Bool

    newsBraidCanProposeCandidateRefsIsTrue :
      newsBraidCanProposeCandidateRefs ≡ true

    resolvedBeforeCommit :
      Bool

    resolvedBeforeCommitIsFalse :
      resolvedBeforeCommit ≡ false

    selectedBeforeCommit :
      Bool

    selectedBeforeCommitIsFalse :
      selectedBeforeCommit ≡ false

    itirValidatedBeforeCommit :
      Bool

    itirValidatedBeforeCommitIsFalse :
      itirValidatedBeforeCommit ≡ false

    commitAllowed :
      Bool

    commitAllowedIsFalse :
      commitAllowed ≡ false

    commitGates :
      List TransportCommitGate

    commitGatesAreCanonical :
      commitGates ≡ canonicalNewsEventCommitGates

    candidateStatement :
      String

    candidateStatementIsCanonical :
      candidateStatement ≡ newsBraidCandidateStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ transportBoundaryStatement

    sourceAuthorityPromotion :
      Bool

    sourceAuthorityPromotionIsFalse :
      sourceAuthorityPromotion ≡ false

    policyAuthorityPromotion :
      Bool

    policyAuthorityPromotionIsFalse :
      policyAuthorityPromotion ≡ false

    wikidataAuthorityPromotion :
      Bool

    wikidataAuthorityPromotionIsFalse :
      wikidataAuthorityPromotion ≡ false

    runtimeITIRPromotion :
      Bool

    runtimeITIRPromotionIsFalse :
      runtimeITIRPromotion ≡ false

    physicsPromotion :
      Bool

    physicsPromotionIsFalse :
      physicsPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    promotionFlags :
      List PNFBraidTransportPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nonClaims :
      List PNFBraidTransportNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalPNFBraidTransportNonClaims

    noPromotion :
      PNFBraidTransportPromotion →
      ⊥

    receiptBoundary :
      List String

open PNFBraidTransportFieldReceipt public

canonicalPNFBraidTransportFieldReceipt :
  PNFBraidTransportFieldReceipt
canonicalPNFBraidTransportFieldReceipt =
  record
    { status =
        pnfBraidTransportRecordedNoPromotion
    ; statusIsCanonical =
        refl
    ; importedSpectralCoreAcknowledged =
        true
    ; importedSpectralCoreAcknowledgedIsTrue =
        refl
    ; braidSourceEvent =
        canonicalNewsSourceEvent
    ; braidSourceEventIsCanonical =
        refl
    ; receiptInitialSlice =
        canonicalInitialSlice
    ; receiptInitialSliceIsCanonical =
        refl
    ; receiptRevisionSlice =
        canonicalRevisionSlice
    ; receiptRevisionSliceIsCanonical =
        refl
    ; crossingKinds =
        canonicalCrossingKinds
    ; crossingKindsAreCanonical =
        refl
    ; candidateRefs =
        canonicalSourceRef ∷ canonicalTargetRef ∷ canonicalFallbackRef ∷ []
    ; candidateRefsAreCanonical =
        refl
    ; fibres =
        canonicalSourceFibre ∷ canonicalTargetFibre ∷ canonicalFallbackFibre ∷ []
    ; fibresAreCanonical =
        refl
    ; braidPathReceipt =
        canonicalNewsBraidPath
    ; braidPathReceiptIsCanonical =
        refl
    ; braidSignatureReceipt =
        canonicalNewsBraidSignature
    ; braidSignatureReceiptIsCanonical =
        refl
    ; transportReceipt =
        canonicalNewsEventTransportReceipt
    ; transportReceiptIsCanonical =
        refl
    ; transportRelation =
        canonicalNewsEventTransportRelation
    ; transportRelationIsCanonical =
        refl
    ; transportRelationIsReceiptBearing =
        true
    ; transportRelationIsReceiptBearingIsTrue =
        refl
    ; transportRelationAssertsTruth =
        false
    ; transportRelationAssertsTruthIsFalse =
        refl
    ; newsBraidCanProposeCandidateRefs =
        true
    ; newsBraidCanProposeCandidateRefsIsTrue =
        refl
    ; resolvedBeforeCommit =
        false
    ; resolvedBeforeCommitIsFalse =
        refl
    ; selectedBeforeCommit =
        false
    ; selectedBeforeCommitIsFalse =
        refl
    ; itirValidatedBeforeCommit =
        false
    ; itirValidatedBeforeCommitIsFalse =
        refl
    ; commitAllowed =
        false
    ; commitAllowedIsFalse =
        refl
    ; commitGates =
        canonicalNewsEventCommitGates
    ; commitGatesAreCanonical =
        refl
    ; candidateStatement =
        newsBraidCandidateStatement
    ; candidateStatementIsCanonical =
        refl
    ; boundaryStatement =
        transportBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; sourceAuthorityPromotion =
        false
    ; sourceAuthorityPromotionIsFalse =
        refl
    ; policyAuthorityPromotion =
        false
    ; policyAuthorityPromotionIsFalse =
        refl
    ; wikidataAuthorityPromotion =
        false
    ; wikidataAuthorityPromotionIsFalse =
        refl
    ; runtimeITIRPromotion =
        false
    ; runtimeITIRPromotionIsFalse =
        refl
    ; physicsPromotion =
        false
    ; physicsPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; nonClaims =
        canonicalPNFBraidTransportNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; noPromotion =
        pnfBraidTransportPromotionImpossible
    ; receiptBoundary =
        "Source event, time slice/revision, strand, crossing kind, braid path, and braid signature are named surfaces"
        ∷ "Crossing kinds include same-fibre, partial residual, contradiction, support strengthening, support weakening, and source continuation"
        ∷ "Transport is a receipt-bearing relation over PNF refs/fibres, not truth"
        ∷ "A news event braid may propose candidate refs only"
        ∷ "Commit is blocked until resolved, selected, and ITIR-validated receipts exist"
        ∷ "Authority and promotion flags remain false"
        ∷ []
    }
