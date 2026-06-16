module DASHI.Interop.PNFResolverSelectorCommitment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFSpectralFieldArchitectureReceipt as Architecture
import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFPackageCore as PackageCore
import DASHI.Interop.PNFSpectralVectorIndex as Vector
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.VectorNonAuthorityCore as VectorNA

------------------------------------------------------------------------
-- Resolver / selector / ITIR commitment package receipt.
--
-- This module refines the vector-index boundary into a commitment package
-- surface for sections 15, 16, 17, 21, 22, and 29 of the intake formalism.
-- Vector and ANN rows may propose candidates.  Resolver receipts may anchor
-- them.  Selector packages may admit structured objects, residual edges,
-- spans, contradiction receipts, provenance, and traces.  ITIR commitment may
-- consume only admitted selector packages, never unresolved candidates or raw
-- vector hits.

data ResolverSelectorCommitmentStatus : Set where
  resolverSelectorCommitmentReceipt_checkedNoANNPromotion :
    ResolverSelectorCommitmentStatus

data FormalismSection : Set where
  section15ResolvePrecondition :
    FormalismSection

  section16SelectorPackage :
    FormalismSection

  section17RejectionAndContradiction :
    FormalismSection

  section21QueryModes :
    FormalismSection

  section22HybridRanking :
    FormalismSection

  section29ITIRCommitment :
    FormalismSection

canonicalFormalismSections : List FormalismSection
canonicalFormalismSections =
  section15ResolvePrecondition
  ∷ section16SelectorPackage
  ∷ section17RejectionAndContradiction
  ∷ section21QueryModes
  ∷ section22HybridRanking
  ∷ section29ITIRCommitment
  ∷ []

------------------------------------------------------------------------
-- Section 15: resolve precondition receipt.

record ResolvePreconditionReceipt : Set where
  constructor resolvePreconditionReceipt
  field
    candidate :
      Vector.CandidateRef

    sourceSearch :
      Vector.VectorSearchReceipt

    resolverProfile :
      String

    candidateIsReferenceOnly :
      Bool

    resolverHasTypedObjectRef :
      Bool

    unresolvedCandidateSupport :
      Bool

    rawVectorHitEvidence :
      Bool

    vectorScoreAsResolveAuthority :
      Bool

    resolveMayAnchorOnly :
      Bool

    candidateReferenceOnlyIsTrue :
      candidateIsReferenceOnly ≡ true

    resolverHasTypedObjectRefIsTrue :
      resolverHasTypedObjectRef ≡ true

    unresolvedCandidateSupportIsFalse :
      unresolvedCandidateSupport ≡ false

    rawVectorHitEvidenceIsFalse :
      rawVectorHitEvidence ≡ false

    vectorScoreAsResolveAuthorityIsFalse :
      vectorScoreAsResolveAuthority ≡ false

    resolveMayAnchorOnlyIsTrue :
      resolveMayAnchorOnly ≡ true

open ResolvePreconditionReceipt public

resolvePreconditionToAnchor :
  ResolvePreconditionReceipt →
  Vector.ResolverAnchor
resolvePreconditionToAnchor receipt =
  Vector.anchorCandidate
    (resolverProfile receipt)
    (candidate receipt)

resolvePreconditionAnchorDoesNotCommitSupport :
  ∀ receipt →
  Vector.resolverCommittedSupport
    (resolvePreconditionToAnchor receipt)
  ≡
  false
resolvePreconditionAnchorDoesNotCommitSupport _ =
  refl

------------------------------------------------------------------------
-- Section 16: selector admission package.

record AdmittedObject : Set where
  constructor admittedObject
  field
    objectRef :
      Core.PredicateObjectRef

    objectSource :
      Vector.ObjectRef

    admittedByResolver :
      Vector.ResolverAnchor

    objectIsResolved :
      Bool

    objectCameFromUnresolvedCandidate :
      Bool

open AdmittedObject public

record AdmittedResidualEdge : Set where
  constructor admittedResidualEdge
  field
    edgeRef :
      Core.ResidualEdgeRef

    edgeLevel :
      Residual.ResidualLevel

    edgeSource :
      Core.PredicateObjectRef

    edgeTarget :
      Core.PredicateObjectRef

    edgeAdmitted :
      Bool

    edgeFromRawVectorHit :
      Bool

open AdmittedResidualEdge public

record SpanReceipt : Set where
  constructor spanReceipt
  field
    spanLabel :
      String

    spanObject :
      Core.PredicateObjectRef

    spanHasPNFCarrier :
      Bool

    spanIsRuntimeEvidence :
      Bool

open SpanReceipt public

record ContradictionReceipt : Set where
  constructor contradictionReceipt
  field
    contradictionLabel :
      String

    contradictionLevel :
      Residual.ResidualLevel

    contradictionRecorded :
      Bool

    contradictionErased :
      Bool

open ContradictionReceipt public

record ProvenanceReceipt : Set where
  constructor provenanceReceipt
  field
    provenanceLabel :
      String

    provenanceSource :
      String

    provenanceRecorded :
      Bool

    provenanceAsAuthority :
      Bool

open ProvenanceReceipt public

data SelectionTraceStep : Set where
  traceCandidateReturned :
    SelectionTraceStep

  traceResolverAnchored :
    SelectionTraceStep

  traceResidualChecked :
    SelectionTraceStep

  traceSpanRecorded :
    SelectionTraceStep

  traceContradictionPreserved :
    SelectionTraceStep

  traceSelectorAdmitted :
    SelectionTraceStep

canonicalSelectionTraceSteps : List SelectionTraceStep
canonicalSelectionTraceSteps =
  traceCandidateReturned
  ∷ traceResolverAnchored
  ∷ traceResidualChecked
  ∷ traceSpanRecorded
  ∷ traceContradictionPreserved
  ∷ traceSelectorAdmitted
  ∷ []

record SelectionTrace : Set where
  constructor selectionTrace
  field
    traceProfile :
      String

    traceSteps :
      List SelectionTraceStep

    traceComplete :
      Bool

    traceUsesScoreAsAuthority :
      Bool

open SelectionTrace public

record SelectorPackage : Set where
  constructor selectorPackage
  field
    selectorAdmission :
      Vector.SelectorAdmission

    admittedObjects :
      List AdmittedObject

    admittedResidualEdges :
      List AdmittedResidualEdge

    spanReceipts :
      List SpanReceipt

    contradictionReceipts :
      List ContradictionReceipt

    provenanceReceipts :
      List ProvenanceReceipt

    packageSelectionTrace :
      SelectionTrace

    packageAdmitted :
      Bool

    allObjectsResolved :
      Bool

    residualEdgesAdmitted :
      Bool

    spansRecorded :
      Bool

    contradictionsPreserved :
      Bool

    provenanceRecorded :
      Bool

    packageUsesVectorProximityAsAdmissibility :
      Bool

    packageCommitsITIRDirectly :
      Bool

    packageAdmittedIsTrue :
      packageAdmitted ≡ true

    allObjectsResolvedIsTrue :
      allObjectsResolved ≡ true

    residualEdgesAdmittedIsTrue :
      residualEdgesAdmitted ≡ true

    spansRecordedIsTrue :
      spansRecorded ≡ true

    contradictionsPreservedIsTrue :
      contradictionsPreserved ≡ true

    provenanceRecordedIsTrue :
      provenanceRecorded ≡ true

    packageUsesVectorProximityAsAdmissibilityIsFalse :
      packageUsesVectorProximityAsAdmissibility ≡ false

    packageCommitsITIRDirectlyIsFalse :
      packageCommitsITIRDirectly ≡ false

open SelectorPackage public

------------------------------------------------------------------------
-- Section 17: rejection reasons and false contradiction erasure gate.

data RejectionReason : Set where
  unresolvedCandidate :
    RejectionReason

  rawVectorHitOnly :
    RejectionReason

  missingResolverAnchor :
    RejectionReason

  missingTypedSpan :
    RejectionReason

  contradictionWouldBeErased :
    RejectionReason

  scoreClaimedAsAuthority :
    RejectionReason

  directANNToITIRAttempt :
    RejectionReason

canonicalRejectionReasons : List RejectionReason
canonicalRejectionReasons =
  unresolvedCandidate
  ∷ rawVectorHitOnly
  ∷ missingResolverAnchor
  ∷ missingTypedSpan
  ∷ contradictionWouldBeErased
  ∷ scoreClaimedAsAuthority
  ∷ directANNToITIRAttempt
  ∷ []

record RejectionReceipt : Set where
  constructor rejectionReceipt
  field
    rejectedCandidate :
      Vector.CandidateRef

    rejectionReason :
      RejectionReason

    rejectionRecorded :
      Bool

    rejectionPromotesSupport :
      Bool

open RejectionReceipt public

------------------------------------------------------------------------
-- Section 21: query modes A-D.

data QueryMode : Set where
  modeAExactObjectLookup :
    QueryMode

  modeBResidualNeighborhood :
    QueryMode

  modeCHybridSpectralNavigation :
    QueryMode

  modeDITIRCommitmentRequest :
    QueryMode

canonicalQueryModes : List QueryMode
canonicalQueryModes =
  modeAExactObjectLookup
  ∷ modeBResidualNeighborhood
  ∷ modeCHybridSpectralNavigation
  ∷ modeDITIRCommitmentRequest
  ∷ []

record QueryModeReceipt : Set where
  constructor queryModeReceipt
  field
    mode :
      QueryMode

    modeLabel :
      String

    mayUseVectorIndex :
      Bool

    mustResolveBeforeSelect :
      Bool

    mustSelectBeforeCommit :
      Bool

    modeProvidesTruth :
      Bool

    modeProvidesRawSupport :
      Bool

open QueryModeReceipt public

canonicalModeAReceipt : QueryModeReceipt
canonicalModeAReceipt =
  queryModeReceipt
    modeAExactObjectLookup
    "A: exact object lookup"
    false
    true
    true
    false
    false

canonicalModeBReceipt : QueryModeReceipt
canonicalModeBReceipt =
  queryModeReceipt
    modeBResidualNeighborhood
    "B: residual neighborhood"
    false
    true
    true
    false
    false

canonicalModeCReceipt : QueryModeReceipt
canonicalModeCReceipt =
  queryModeReceipt
    modeCHybridSpectralNavigation
    "C: hybrid spectral navigation"
    true
    true
    true
    false
    false

canonicalModeDReceipt : QueryModeReceipt
canonicalModeDReceipt =
  queryModeReceipt
    modeDITIRCommitmentRequest
    "D: ITIR commitment request"
    false
    true
    true
    false
    false

canonicalQueryModeReceipts : List QueryModeReceipt
canonicalQueryModeReceipts =
  canonicalModeAReceipt
  ∷ canonicalModeBReceipt
  ∷ canonicalModeCReceipt
  ∷ canonicalModeDReceipt
  ∷ []

------------------------------------------------------------------------
-- Section 22: hybrid ranking is ordering-only.

data RankingSignal : Set where
  lexicalMatchSignal :
    RankingSignal

  residualSeveritySignal :
    RankingSignal

  spectralProximitySignal :
    RankingSignal

  provenanceFreshnessSignal :
    RankingSignal

canonicalRankingSignals : List RankingSignal
canonicalRankingSignals =
  lexicalMatchSignal
  ∷ residualSeveritySignal
  ∷ spectralProximitySignal
  ∷ provenanceFreshnessSignal
  ∷ []

record HybridRankingReceipt : Set where
  constructor hybridRankingReceipt
  field
    rankingProfile :
      String

    rankingSignals :
      List RankingSignal

    orderingOnly :
      Bool

    scoreAsAuthority :
      Bool

    rankingCommitsSupport :
      Bool

    rankingErasesContradictions :
      Bool

    orderingOnlyIsTrue :
      orderingOnly ≡ true

    scoreAsAuthorityIsFalse :
      scoreAsAuthority ≡ false

    rankingCommitsSupportIsFalse :
      rankingCommitsSupport ≡ false

    rankingErasesContradictionsIsFalse :
      rankingErasesContradictions ≡ false

open HybridRankingReceipt public

canonicalHybridRankingReceipt : HybridRankingReceipt
canonicalHybridRankingReceipt =
  hybridRankingReceipt
    "canonical-hybrid-ranking-ordering-only"
    canonicalRankingSignals
    true
    false
    false
    false
    refl
    refl
    refl
    refl

rankingCoreAdapterProposal : VectorNA.VectorProposalRow
rankingCoreAdapterProposal =
  VectorNA.vectorProposalRow
    VectorNA.rankingProposalMode
    VectorNA.canonicalCandidateOnlyHit
    VectorNA.canonicalVectorEvidenceClaim
    VectorNA.fallbackVectorCoordinate
    VectorNA.fallbackVectorCoordinate
    VectorNA.fallbackObjectRef
    "resolver-selector-ranking-ordering-only-core-adapter"
    true
    false
    false
    false
    false

rankingCoreAdapterProposalReceipt :
  VectorNA.VectorProposalRowReceipt rankingCoreAdapterProposal
rankingCoreAdapterProposalReceipt =
  VectorNA.vectorProposalRowReceipt
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Product commitment certificate: resolved and corroborated candidates.

data ResidualCheckShape : Set where
  residualExactCheck :
    ResidualCheckShape

  residualPartialCheck :
    ResidualCheckShape

canonicalResidualCheckShapes : List ResidualCheckShape
canonicalResidualCheckShapes =
  residualExactCheck
  ∷ residualPartialCheck
  ∷ []

record CandidateResidualCheckReceipt : Set where
  constructor candidateResidualCheckReceipt
  field
    checkedAnchor :
      Vector.ResolverAnchor

    checkedResidualLevel :
      Residual.ResidualLevel

    residualCheckShape :
      ResidualCheckShape

    residualChecked :
      Bool

    residualExactOrPartial :
      Bool

    exactResidualAccepted :
      Bool

    partialResidualAccepted :
      Bool

    noTypedMeetAccepted :
      Bool

    contradictionAcceptedAsCorroboration :
      Bool

    residualCheckedIsTrue :
      residualChecked ≡ true

    residualExactOrPartialIsTrue :
      residualExactOrPartial ≡ true

    exactResidualAcceptedIsFalse :
      exactResidualAccepted ≡ false

    partialResidualAcceptedIsTrue :
      partialResidualAccepted ≡ true

    noTypedMeetAcceptedIsFalse :
      noTypedMeetAccepted ≡ false

    contradictionAcceptedAsCorroborationIsFalse :
      contradictionAcceptedAsCorroboration ≡ false

open CandidateResidualCheckReceipt public

record ResolverSelectorProductCommitmentCertificate : Set where
  constructor resolverSelectorProductCommitmentCertificate
  field
    productCandidate :
      Vector.CandidateRef

    productSearch :
      Vector.VectorSearchReceipt

    productResolverAnchor :
      Vector.ResolverAnchor

    productResidualCheck :
      CandidateResidualCheckReceipt

    productSpanReceipt :
      SpanReceipt

    productProvenanceReceipt :
      ProvenanceReceipt

    productSelectorPackage :
      SelectorPackage

    candidateFromVectorSearch :
      Bool

    spectralProximityRecorded :
      Bool

    resolverAnchorRecorded :
      Bool

    residualExactOrPartialRecorded :
      Bool

    spanReceiptAnchored :
      Bool

    receiptAnchoringRecorded :
      Bool

    admittedPackageRecorded :
      Bool

    corroboratedCandidate :
      Bool

    supportFromVector :
      Bool

    truthFromVector :
      Bool

    admissibilityFromVector :
      Bool

    unresolvedCandidateCanCommitSupport :
      Bool

    vectorScoreCanCommitSupport :
      Bool

    rawHitCanCommitSupport :
      Bool

    productCandidateMatchesAnchor :
      Vector.anchoredCandidate productResolverAnchor ≡ productCandidate

    productAnchorMatchesResidualCheck :
      checkedAnchor productResidualCheck ≡ productResolverAnchor

    productAnchorMatchesSelector :
      Vector.selectedAnchor
        (selectorAdmission productSelectorPackage)
      ≡
      productResolverAnchor

    productResidualMatchesSelector :
      Vector.residualLevel
        (selectorAdmission productSelectorPackage)
      ≡
      checkedResidualLevel productResidualCheck

    candidateFromVectorSearchIsTrue :
      candidateFromVectorSearch ≡ true

    spectralProximityRecordedIsTrue :
      spectralProximityRecorded ≡ true

    resolverAnchorRecordedIsTrue :
      resolverAnchorRecorded ≡ true

    residualExactOrPartialRecordedIsTrue :
      residualExactOrPartialRecorded ≡ true

    spanReceiptAnchoredIsTrue :
      spanReceiptAnchored ≡ true

    receiptAnchoringRecordedIsTrue :
      receiptAnchoringRecorded ≡ true

    admittedPackageRecordedIsTrue :
      admittedPackageRecorded ≡ true

    corroboratedCandidateIsTrue :
      corroboratedCandidate ≡ true

    supportFromVectorIsFalse :
      supportFromVector ≡ false

    truthFromVectorIsFalse :
      truthFromVector ≡ false

    admissibilityFromVectorIsFalse :
      admissibilityFromVector ≡ false

    unresolvedCandidateCanCommitSupportIsFalse :
      unresolvedCandidateCanCommitSupport ≡ false

    vectorScoreCanCommitSupportIsFalse :
      vectorScoreCanCommitSupport ≡ false

    rawHitCanCommitSupportIsFalse :
      rawHitCanCommitSupport ≡ false

open ResolverSelectorProductCommitmentCertificate public

------------------------------------------------------------------------
-- Section 29: ITIR commitment may consume only admitted packages.

record ITIRPackageCommitmentReceipt : Set where
  constructor itirPackageCommitmentReceipt
  field
    committedPackage :
      SelectorPackage

    commitReceipt :
      Vector.ITIRCommitReceipt

    commitmentProfile :
      String

    consumesOnlyAdmittedPackages :
      Bool

    consumesResolverAnchor :
      Bool

    consumesSelectorAdmission :
      Bool

    consumesUnresolvedCandidate :
      Bool

    consumesRawVectorHitEvidence :
      Bool

    directANNToITIRCommitment :
      Bool

    consumesOnlyAdmittedPackagesIsTrue :
      consumesOnlyAdmittedPackages ≡ true

    consumesResolverAnchorIsTrue :
      consumesResolverAnchor ≡ true

    consumesSelectorAdmissionIsTrue :
      consumesSelectorAdmission ≡ true

    consumesUnresolvedCandidateIsFalse :
      consumesUnresolvedCandidate ≡ false

    consumesRawVectorHitEvidenceIsFalse :
      consumesRawVectorHitEvidence ≡ false

    directANNToITIRCommitmentIsFalse :
      directANNToITIRCommitment ≡ false

open ITIRPackageCommitmentReceipt public

data DirectANNToITIRCommitment : Set where

directANNToITIRCommitmentImpossible :
  DirectANNToITIRCommitment →
  ⊥
directANNToITIRCommitmentImpossible ()

------------------------------------------------------------------------
-- Canonical false gates.

unresolvedCandidateSupportGate : Bool
unresolvedCandidateSupportGate =
  false

rawVectorHitEvidenceGate : Bool
rawVectorHitEvidenceGate =
  false

scoreAsAuthorityGate : Bool
scoreAsAuthorityGate =
  false

contradictionErasureGate : Bool
contradictionErasureGate =
  false

directANNToITIRCommitmentGate : Bool
directANNToITIRCommitmentGate =
  false

------------------------------------------------------------------------
-- Canonical example package.

canonicalResolvePreconditionReceipt : ResolvePreconditionReceipt
canonicalResolvePreconditionReceipt =
  resolvePreconditionReceipt
    Vector.canonicalSampleCandidate
    Vector.canonicalSampleSearchReceipt
    "canonical-resolver-v1"
    true
    true
    false
    false
    false
    true
    refl
    refl
    refl
    refl
    refl
    refl

canonicalResolvedAnchor : Vector.ResolverAnchor
canonicalResolvedAnchor =
  resolvePreconditionToAnchor canonicalResolvePreconditionReceipt

canonicalAdmittedObject : AdmittedObject
canonicalAdmittedObject =
  admittedObject
    Core.canonicalPredicateObjectRef
    Vector.canonicalSampleObject
    canonicalResolvedAnchor
    true
    false

canonicalAdmittedResidualEdge : AdmittedResidualEdge
canonicalAdmittedResidualEdge =
  admittedResidualEdge
    Core.residualEdgeFallback
    Residual.partial
    Core.canonicalPredicateObjectRef
    Core.canonicalPredicateObjectRef
    true
    false

canonicalSpanReceipt : SpanReceipt
canonicalSpanReceipt =
  spanReceipt
    "canonical-span"
    Core.canonicalPredicateObjectRef
    true
    false

canonicalContradictionReceipt : ContradictionReceipt
canonicalContradictionReceipt =
  contradictionReceipt
    "canonical-contradiction-preserved"
    Residual.contradiction
    true
    false

canonicalProvenanceReceipt : ProvenanceReceipt
canonicalProvenanceReceipt =
  provenanceReceipt
    "canonical-provenance"
    "receipt-local"
    true
    false

canonicalSelectionTrace : SelectionTrace
canonicalSelectionTrace =
  selectionTrace
    "canonical-selection-trace"
    canonicalSelectionTraceSteps
    true
    false

canonicalSelectorAdmission : Vector.SelectorAdmission
canonicalSelectorAdmission =
  Vector.admitAnchoredCandidate
    "canonical-selector-v1"
    canonicalResolvedAnchor
    Residual.partial

canonicalSelectorPackage : SelectorPackage
canonicalSelectorPackage =
  selectorPackage
    canonicalSelectorAdmission
    (canonicalAdmittedObject ∷ [])
    (canonicalAdmittedResidualEdge ∷ [])
    (canonicalSpanReceipt ∷ [])
    (canonicalContradictionReceipt ∷ [])
    (canonicalProvenanceReceipt ∷ [])
    canonicalSelectionTrace
    true
    true
    true
    true
    true
    true
    false
    false
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalCandidateResidualCheckReceipt : CandidateResidualCheckReceipt
canonicalCandidateResidualCheckReceipt =
  candidateResidualCheckReceipt
    canonicalResolvedAnchor
    Residual.partial
    residualPartialCheck
    true
    true
    false
    true
    false
    false
    refl
    refl
    refl
    refl
    refl
    refl

canonicalProductCommitmentCertificate :
  ResolverSelectorProductCommitmentCertificate
canonicalProductCommitmentCertificate =
  resolverSelectorProductCommitmentCertificate
    Vector.canonicalSampleCandidate
    Vector.canonicalSampleSearchReceipt
    canonicalResolvedAnchor
    canonicalCandidateResidualCheckReceipt
    canonicalSpanReceipt
    canonicalProvenanceReceipt
    canonicalSelectorPackage
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
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
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalITIRCommitReceipt : Vector.ITIRCommitReceipt
canonicalITIRCommitReceipt =
  Vector.commitAdmittedSelection
    "canonical-itir-v1"
    canonicalSelectorAdmission

canonicalITIRPackageCommitmentReceipt : ITIRPackageCommitmentReceipt
canonicalITIRPackageCommitmentReceipt =
  itirPackageCommitmentReceipt
    canonicalSelectorPackage
    canonicalITIRCommitReceipt
    "canonical-itir-package-commitment"
    true
    true
    true
    false
    false
    false
    refl
    refl
    refl
    refl
    refl
    refl

canonicalArchitectureContext :
  Architecture.PNFSpectralFieldArchitectureReceipt
canonicalArchitectureContext =
  Architecture.canonicalPNFSpectralFieldArchitectureReceipt

resolverSelectorCommitmentStatement : String
resolverSelectorCommitmentStatement =
  "Resolver/selector/ITIR commitment consumes typed resolved selector packages only: unresolved candidate support, raw vector hit evidence, score-as-authority, contradiction erasure, and direct ANN-to-ITIR commitment are false gates."

record PNFResolverSelectorCommitmentReceipt : Set where
  constructor pnfResolverSelectorCommitmentReceipt
  field
    status :
      ResolverSelectorCommitmentStatus

    sections :
      List FormalismSection

    architectureContext :
      Architecture.PNFSpectralFieldArchitectureReceipt

    resolvePrecondition :
      ResolvePreconditionReceipt

    selectorPackageReceipt :
      SelectorPackage

    rejectionReasons :
      List RejectionReason

    queryModes :
      List QueryMode

    queryModeReceipts :
      List QueryModeReceipt

    hybridRanking :
      HybridRankingReceipt

    productCommitmentCertificate :
      ResolverSelectorProductCommitmentCertificate

    itirCommitment :
      ITIRPackageCommitmentReceipt

    pnfPackageCoreAdapter :
      PackageCore.SelectorPackage

    pnfPackageCoreAdapterIsCanonical :
      pnfPackageCoreAdapter
      ≡
      PackageCore.canonicalAdmittedSelectorPackage

    pnfPackageCoreDirectCommitFalse :
      PackageCore.selectorCommitsDirectlyToITIR
        pnfPackageCoreAdapter
      ≡
      false

    vectorNonAuthorityCoreAdapter :
      VectorNA.VectorNonAuthorityReceipt

    vectorNonAuthorityCoreAdapterIsCanonical :
      vectorNonAuthorityCoreAdapter
      ≡
      VectorNA.canonicalVectorNonAuthorityReceipt

    vectorNonAuthorityRankingAdapter :
      VectorNA.VectorProposalRow

    vectorNonAuthorityRankingAdapterIsCanonical :
      vectorNonAuthorityRankingAdapter ≡ rankingCoreAdapterProposal

    vectorNonAuthorityCoreTruthFalse :
      VectorNA.proposalRowCarriesTruthAuthority
        vectorNonAuthorityRankingAdapter
      ≡
      false

    vectorNonAuthorityCoreSupportFalse :
      VectorNA.proposalRowCarriesSupportAuthority
        vectorNonAuthorityRankingAdapter
      ≡
      false

    vectorNonAuthorityCoreAdmissibilityFalse :
      VectorNA.proposalRowCarriesAdmissibilityAuthority
        vectorNonAuthorityRankingAdapter
      ≡
      false

    receiptCorroboratedCandidate :
      Bool

    receiptSupportFromVector :
      Bool

    receiptTruthFromVector :
      Bool

    receiptAdmissibilityFromVector :
      Bool

    statement :
      String

    statusIsCanonical :
      status
      ≡
      resolverSelectorCommitmentReceipt_checkedNoANNPromotion

    sectionsAreCanonical :
      sections ≡ canonicalFormalismSections

    architectureContextIsCanonical :
      architectureContext ≡ canonicalArchitectureContext

    resolvePreconditionIsCanonical :
      resolvePrecondition ≡ canonicalResolvePreconditionReceipt

    selectorPackageIsCanonical :
      selectorPackageReceipt ≡ canonicalSelectorPackage

    rejectionReasonsAreCanonical :
      rejectionReasons ≡ canonicalRejectionReasons

    queryModesAreCanonical :
      queryModes ≡ canonicalQueryModes

    queryModeReceiptsAreCanonical :
      queryModeReceipts ≡ canonicalQueryModeReceipts

    hybridRankingIsCanonical :
      hybridRanking ≡ canonicalHybridRankingReceipt

    productCommitmentCertificateIsCanonical :
      productCommitmentCertificate
      ≡
      canonicalProductCommitmentCertificate

    itirCommitmentIsCanonical :
      itirCommitment ≡ canonicalITIRPackageCommitmentReceipt

    receiptCorroboratedCandidateIsTrue :
      receiptCorroboratedCandidate ≡ true

    receiptSupportFromVectorIsFalse :
      receiptSupportFromVector ≡ false

    receiptTruthFromVectorIsFalse :
      receiptTruthFromVector ≡ false

    receiptAdmissibilityFromVectorIsFalse :
      receiptAdmissibilityFromVector ≡ false

    statementIsCanonical :
      statement ≡ resolverSelectorCommitmentStatement

    unresolvedCandidateSupportIsFalse :
      unresolvedCandidateSupportGate ≡ false

    rawVectorHitEvidenceIsFalse :
      rawVectorHitEvidenceGate ≡ false

    scoreAsAuthorityIsFalse :
      scoreAsAuthorityGate ≡ false

    contradictionErasureIsFalse :
      contradictionErasureGate ≡ false

    directANNToITIRCommitmentIsFalse :
      directANNToITIRCommitmentGate ≡ false

open PNFResolverSelectorCommitmentReceipt public

canonicalPNFResolverSelectorCommitmentReceipt :
  PNFResolverSelectorCommitmentReceipt
canonicalPNFResolverSelectorCommitmentReceipt =
  pnfResolverSelectorCommitmentReceipt
    resolverSelectorCommitmentReceipt_checkedNoANNPromotion
    canonicalFormalismSections
    canonicalArchitectureContext
    canonicalResolvePreconditionReceipt
    canonicalSelectorPackage
    canonicalRejectionReasons
    canonicalQueryModes
    canonicalQueryModeReceipts
    canonicalHybridRankingReceipt
    canonicalProductCommitmentCertificate
    canonicalITIRPackageCommitmentReceipt
    PackageCore.canonicalAdmittedSelectorPackage
    refl
    refl
    VectorNA.canonicalVectorNonAuthorityReceipt
    refl
    rankingCoreAdapterProposal
    refl
    refl
    refl
    refl
    true
    false
    false
    false
    resolverSelectorCommitmentStatement
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

canonicalReceipt :
  PNFResolverSelectorCommitmentReceipt
canonicalReceipt =
  canonicalPNFResolverSelectorCommitmentReceipt

------------------------------------------------------------------------
-- Projection lemmas by refl.

canonicalResolvePreconditionProjection :
  resolvePrecondition canonicalReceipt
  ≡
  canonicalResolvePreconditionReceipt
canonicalResolvePreconditionProjection =
  refl

canonicalSelectorPackageProjection :
  selectorPackageReceipt canonicalReceipt
  ≡
  canonicalSelectorPackage
canonicalSelectorPackageProjection =
  refl

canonicalHybridRankingProjection :
  hybridRanking canonicalReceipt
  ≡
  canonicalHybridRankingReceipt
canonicalHybridRankingProjection =
  refl

canonicalProductCommitmentCertificateProjection :
  productCommitmentCertificate canonicalReceipt
  ≡
  canonicalProductCommitmentCertificate
canonicalProductCommitmentCertificateProjection =
  refl

canonicalITIRCommitmentProjection :
  itirCommitment canonicalReceipt
  ≡
  canonicalITIRPackageCommitmentReceipt
canonicalITIRCommitmentProjection =
  refl

canonicalPackageConsumesOnlyAdmittedPackages :
  consumesOnlyAdmittedPackages
    (itirCommitment canonicalReceipt)
  ≡
  true
canonicalPackageConsumesOnlyAdmittedPackages =
  refl

canonicalPackageRejectsRawVectorHitEvidence :
  consumesRawVectorHitEvidence
    (itirCommitment canonicalReceipt)
  ≡
  false
canonicalPackageRejectsRawVectorHitEvidence =
  refl

canonicalPackageRejectsDirectANNToITIR :
  directANNToITIRCommitment
    (itirCommitment canonicalReceipt)
  ≡
  false
canonicalPackageRejectsDirectANNToITIR =
  refl

canonicalReceiptCorroboratedCandidateTrue :
  receiptCorroboratedCandidate canonicalReceipt ≡ true
canonicalReceiptCorroboratedCandidateTrue =
  refl

canonicalReceiptSupportFromVectorFalse :
  receiptSupportFromVector canonicalReceipt ≡ false
canonicalReceiptSupportFromVectorFalse =
  refl

canonicalReceiptTruthFromVectorFalse :
  receiptTruthFromVector canonicalReceipt ≡ false
canonicalReceiptTruthFromVectorFalse =
  refl

canonicalReceiptAdmissibilityFromVectorFalse :
  receiptAdmissibilityFromVector canonicalReceipt ≡ false
canonicalReceiptAdmissibilityFromVectorFalse =
  refl

canonicalRankingIsOrderingOnly :
  orderingOnly (hybridRanking canonicalReceipt)
  ≡
  true
canonicalRankingIsOrderingOnly =
  refl

canonicalRankingScoreIsNotAuthority :
  scoreAsAuthority (hybridRanking canonicalReceipt)
  ≡
  false
canonicalRankingScoreIsNotAuthority =
  refl

canonicalRankingCoreAdapterScoreAuthorityFalse :
  scoreAsAuthority (hybridRanking canonicalReceipt) ≡ false
canonicalRankingCoreAdapterScoreAuthorityFalse =
  refl

canonicalReceiptVectorNonAuthorityRankingTruthFalse :
  VectorNA.proposalRowCarriesTruthAuthority
    (vectorNonAuthorityRankingAdapter canonicalReceipt)
  ≡
  false
canonicalReceiptVectorNonAuthorityRankingTruthFalse =
  refl

canonicalContradictionIsPreserved :
  contradictionErased canonicalContradictionReceipt
  ≡
  false
canonicalContradictionIsPreserved =
  refl
