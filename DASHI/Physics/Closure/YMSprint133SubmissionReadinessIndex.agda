module DASHI.Physics.Closure.YMSprint133SubmissionReadinessIndex where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint131SubmissionPacketManifest
  as S131-MANIFEST
import DASHI.Physics.Closure.YMSprint132RedTeamObjectionResolutionLedger
  as S132-REDTEAM
import DASHI.Physics.Closure.YMSprint132ReproducibilityBoundaryLedger
  as S132-REPRO

------------------------------------------------------------------------
-- Sprint133 submission-readiness index.
--
-- This receipt indexes the concrete Sprint131 submission packet manifest
-- and Sprint132 red-team/reproducibility ledgers into terminal readiness
-- rows.  Internal packet readiness is true.  External governance and
-- acceptance are absent.  Clay Yang-Mills promotion remains false.

sprintNumber : Nat
sprintNumber = 133

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint133SubmissionReadinessIndex.agda"

indexName : String
indexName =
  "Sprint133 submission-readiness index"

indexLane : String
indexLane =
  "Sprint133-submission-readiness-index"

sourceSprint131ManifestPath : String
sourceSprint131ManifestPath = S131-MANIFEST.modulePath

sourceSprint132RedTeamPath : String
sourceSprint132RedTeamPath = S132-REDTEAM.modulePath

sourceSprint132ReproducibilityPath : String
sourceSprint132ReproducibilityPath = S132-REPRO.modulePath

indexRecorded : Bool
indexRecorded = true

submissionPacketManifestImported : Bool
submissionPacketManifestImported = S131-MANIFEST.manifestRecorded

redTeamLedgerImported : Bool
redTeamLedgerImported = S132-REDTEAM.redTeamReceiptComplete

reproducibilityLedgerImported : Bool
reproducibilityLedgerImported = S132-REPRO.ledgerRecorded

internalPacketReady : Bool
internalPacketReady = S131-MANIFEST.internalSubmissionPacketReady

internalCandidateReady : Bool
internalCandidateReady = S131-MANIFEST.internalCandidatePacketReady

internalRedTeamResolved : Bool
internalRedTeamResolved = S132-REDTEAM.internalObjectionsResolved

internalReproducibilityVerified : Bool
internalReproducibilityVerified =
  S132-REPRO.internalReproducibilityVerified

externalGovernanceComplete : Bool
externalGovernanceComplete = S132-REPRO.externalGovernanceComplete

externalAcceptanceTokenPresent : Bool
externalAcceptanceTokenPresent =
  S131-MANIFEST.externalAcceptanceTokenPresent

externalAcceptanceAbsent : Bool
externalAcceptanceAbsent = false

externalGovernanceAbsent : Bool
externalGovernanceAbsent = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

indexRecordedIsTrue : indexRecorded ≡ true
indexRecordedIsTrue = refl

submissionPacketManifestImportedIsTrue :
  submissionPacketManifestImported ≡ true
submissionPacketManifestImportedIsTrue =
  S131-MANIFEST.manifestRecordedIsTrue

redTeamLedgerImportedIsTrue :
  redTeamLedgerImported ≡ true
redTeamLedgerImportedIsTrue =
  S132-REDTEAM.redTeamReceiptCompleteIsTrue

reproducibilityLedgerImportedIsTrue :
  reproducibilityLedgerImported ≡ true
reproducibilityLedgerImportedIsTrue =
  S132-REPRO.ledgerRecordedIsTrue

internalPacketReadyIsTrue : internalPacketReady ≡ true
internalPacketReadyIsTrue =
  S131-MANIFEST.internalSubmissionPacketReadyIsTrue

internalCandidateReadyIsTrue : internalCandidateReady ≡ true
internalCandidateReadyIsTrue =
  S131-MANIFEST.internalCandidatePacketReadyIsTrue

internalRedTeamResolvedIsTrue :
  internalRedTeamResolved ≡ true
internalRedTeamResolvedIsTrue =
  S132-REDTEAM.internalObjectionsResolvedIsTrue

internalReproducibilityVerifiedIsTrue :
  internalReproducibilityVerified ≡ true
internalReproducibilityVerifiedIsTrue =
  S132-REPRO.internalReproducibilityVerifiedIsTrue

externalGovernanceCompleteIsFalse :
  externalGovernanceComplete ≡ false
externalGovernanceCompleteIsFalse =
  S132-REPRO.externalGovernanceCompleteIsFalse

externalAcceptanceTokenPresentIsFalse :
  externalAcceptanceTokenPresent ≡ false
externalAcceptanceTokenPresentIsFalse =
  S131-MANIFEST.externalAcceptanceTokenPresentIsFalse

externalAcceptanceAbsentIsFalse :
  externalAcceptanceAbsent ≡ false
externalAcceptanceAbsentIsFalse = refl

externalGovernanceAbsentIsFalse :
  externalGovernanceAbsent ≡ false
externalGovernanceAbsentIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data ReadinessCheck : Set where
  submission-packet-manifest-check :
    ReadinessCheck
  red-team-objection-ledger-check :
    ReadinessCheck
  reproducibility-boundary-ledger-check :
    ReadinessCheck
  internal-packet-readiness-check :
    ReadinessCheck
  external-governance-boundary-check :
    ReadinessCheck
  external-acceptance-boundary-check :
    ReadinessCheck
  clay-promotion-boundary-check :
    ReadinessCheck

data ReadinessStatus : Set where
  imported-evidence-ready :
    ReadinessStatus
  internal-ready :
    ReadinessStatus
  absent-external-governance :
    ReadinessStatus
  absent-external-acceptance :
    ReadinessStatus
  promotion-held-false :
    ReadinessStatus

data ReadinessVerdict : Set where
  ready-in-repository :
    ReadinessVerdict
  absent-outside-repository :
    ReadinessVerdict
  not-promoted :
    ReadinessVerdict

record ReadyRow : Set where
  constructor mkReadyRow
  field
    check :
      ReadinessCheck
    checkCode :
      String
    evidencePath :
      String
    ready :
      Bool
    readyIsTrue :
      ready ≡ true
    status :
      ReadinessStatus
    verdict :
      ReadinessVerdict
    rowText :
      String

record AbsentRow : Set where
  constructor mkAbsentRow
  field
    check :
      ReadinessCheck
    checkCode :
      String
    evidencePath :
      String
    present :
      Bool
    presentIsFalse :
      present ≡ false
    status :
      ReadinessStatus
    verdict :
      ReadinessVerdict
    rowText :
      String

submissionPacketManifestRow : ReadyRow
submissionPacketManifestRow =
  mkReadyRow
    submission-packet-manifest-check
    "S131-manifest-imported"
    sourceSprint131ManifestPath
    submissionPacketManifestImported
    submissionPacketManifestImportedIsTrue
    imported-evidence-ready
    ready-in-repository
    "Sprint131 submission packet manifest is imported as concrete evidence."

redTeamLedgerRow : ReadyRow
redTeamLedgerRow =
  mkReadyRow
    red-team-objection-ledger-check
    "S132-red-team-imported"
    sourceSprint132RedTeamPath
    redTeamLedgerImported
    redTeamLedgerImportedIsTrue
    imported-evidence-ready
    ready-in-repository
    "Sprint132 red-team objection ledger is imported and complete."

reproducibilityLedgerRow : ReadyRow
reproducibilityLedgerRow =
  mkReadyRow
    reproducibility-boundary-ledger-check
    "S132-repro-imported"
    sourceSprint132ReproducibilityPath
    reproducibilityLedgerImported
    reproducibilityLedgerImportedIsTrue
    imported-evidence-ready
    ready-in-repository
    "Sprint132 reproducibility boundary ledger is imported and complete."

internalPacketReadinessRow : ReadyRow
internalPacketReadinessRow =
  mkReadyRow
    internal-packet-readiness-check
    "internal-packet-ready"
    sourceSprint131ManifestPath
    internalPacketReady
    internalPacketReadyIsTrue
    internal-ready
    ready-in-repository
    "Internal submission packet readiness is true in the Sprint131 manifest."

externalGovernanceBoundaryRow : AbsentRow
externalGovernanceBoundaryRow =
  mkAbsentRow
    external-governance-boundary-check
    "external-governance-absent"
    sourceSprint132ReproducibilityPath
    externalGovernanceComplete
    externalGovernanceCompleteIsFalse
    absent-external-governance
    absent-outside-repository
    "External governance completion is absent and remains outside the repository."

externalAcceptanceBoundaryRow : AbsentRow
externalAcceptanceBoundaryRow =
  mkAbsentRow
    external-acceptance-boundary-check
    "external-acceptance-absent"
    sourceSprint131ManifestPath
    externalAcceptanceTokenPresent
    externalAcceptanceTokenPresentIsFalse
    absent-external-acceptance
    absent-outside-repository
    "External acceptance token is absent in the imported submission manifest."

clayPromotionBoundaryRow : AbsentRow
clayPromotionBoundaryRow =
  mkAbsentRow
    clay-promotion-boundary-check
    "clay-yang-mills-promoted-false"
    modulePath
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
    promotion-held-false
    not-promoted
    "Clay Yang-Mills promotion is held false in the Sprint133 index."

readyRows : List ReadyRow
readyRows =
  submissionPacketManifestRow
  ∷ redTeamLedgerRow
  ∷ reproducibilityLedgerRow
  ∷ internalPacketReadinessRow
  ∷ []

absentRows : List AbsentRow
absentRows =
  externalGovernanceBoundaryRow
  ∷ externalAcceptanceBoundaryRow
  ∷ clayPromotionBoundaryRow
  ∷ []

allReadinessChecks : List ReadinessCheck
allReadinessChecks =
  submission-packet-manifest-check
  ∷ red-team-objection-ledger-check
  ∷ reproducibility-boundary-ledger-check
  ∷ internal-packet-readiness-check
  ∷ external-governance-boundary-check
  ∷ external-acceptance-boundary-check
  ∷ clay-promotion-boundary-check
  ∷ []

record ImportedReadinessEvidence : Set where
  constructor mkImportedReadinessEvidence
  field
    sprint131ManifestPath :
      String
    sprint132RedTeamPath :
      String
    sprint132ReproducibilityPath :
      String
    sprint131ManifestImported :
      Bool
    sprint131ManifestImportedIsTrue :
      sprint131ManifestImported ≡ true
    sprint132RedTeamImported :
      Bool
    sprint132RedTeamImportedIsTrue :
      sprint132RedTeamImported ≡ true
    sprint132ReproducibilityImported :
      Bool
    sprint132ReproducibilityImportedIsTrue :
      sprint132ReproducibilityImported ≡ true

canonicalImportedReadinessEvidence : ImportedReadinessEvidence
canonicalImportedReadinessEvidence =
  mkImportedReadinessEvidence
    sourceSprint131ManifestPath
    sourceSprint132RedTeamPath
    sourceSprint132ReproducibilityPath
    submissionPacketManifestImported
    submissionPacketManifestImportedIsTrue
    redTeamLedgerImported
    redTeamLedgerImportedIsTrue
    reproducibilityLedgerImported
    reproducibilityLedgerImportedIsTrue

record ReadinessFlags : Set where
  constructor mkReadinessFlags
  field
    candidateReady :
      Bool
    candidateReadyIsTrue :
      candidateReady ≡ true
    packetReady :
      Bool
    packetReadyIsTrue :
      packetReady ≡ true
    redTeamResolved :
      Bool
    redTeamResolvedIsTrue :
      redTeamResolved ≡ true
    reproducible :
      Bool
    reproducibleIsTrue :
      reproducible ≡ true
    governanceComplete :
      Bool
    governanceCompleteIsFalse :
      governanceComplete ≡ false
    acceptancePresent :
      Bool
    acceptancePresentIsFalse :
      acceptancePresent ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

canonicalReadinessFlags : ReadinessFlags
canonicalReadinessFlags =
  mkReadinessFlags
    internalCandidateReady
    internalCandidateReadyIsTrue
    internalPacketReady
    internalPacketReadyIsTrue
    internalRedTeamResolved
    internalRedTeamResolvedIsTrue
    internalReproducibilityVerified
    internalReproducibilityVerifiedIsTrue
    externalGovernanceComplete
    externalGovernanceCompleteIsFalse
    externalAcceptanceTokenPresent
    externalAcceptanceTokenPresentIsFalse
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse

record YMSprint133SubmissionReadinessIndex : Setω where
  constructor mkYMSprint133SubmissionReadinessIndex
  field
    receiptSprint :
      Nat
    receiptPath :
      String
    receiptName :
      String
    receiptLane :
      String
    importedEvidence :
      ImportedReadinessEvidence
    repositoryReadyRows :
      List ReadyRow
    externalAbsentRows :
      List AbsentRow
    checks :
      List ReadinessCheck
    readinessFlags :
      ReadinessFlags
    terminalStatus :
      ReadinessStatus
    terminalStatement :
      String
    recorded :
      indexRecorded ≡ true
    packetReady :
      internalPacketReady ≡ true
    redTeamResolved :
      internalRedTeamResolved ≡ true
    reproducible :
      internalReproducibilityVerified ≡ true
    governanceAbsent :
      externalGovernanceComplete ≡ false
    acceptanceAbsent :
      externalAcceptanceTokenPresent ≡ false
    clayNotPromoted :
      clayYangMillsPromoted ≡ false

canonicalSprint133SubmissionReadinessIndex :
  YMSprint133SubmissionReadinessIndex
canonicalSprint133SubmissionReadinessIndex =
  mkYMSprint133SubmissionReadinessIndex
    sprintNumber
    modulePath
    indexName
    indexLane
    canonicalImportedReadinessEvidence
    readyRows
    absentRows
    allReadinessChecks
    canonicalReadinessFlags
    promotion-held-false
    "Sprint133 indexes the Sprint131 manifest plus Sprint132 red-team and reproducibility ledgers: internal packet readiness is true, external governance and acceptance are absent, and Clay Yang-Mills promotion is false."
    indexRecordedIsTrue
    internalPacketReadyIsTrue
    internalRedTeamResolvedIsTrue
    internalReproducibilityVerifiedIsTrue
    externalGovernanceCompleteIsFalse
    externalAcceptanceTokenPresentIsFalse
    clayYangMillsPromotedIsFalse

canonicalReceipt : YMSprint133SubmissionReadinessIndex
canonicalReceipt =
  canonicalSprint133SubmissionReadinessIndex

canonicalInternalPacketReady :
  ReadinessFlags.packetReady
    (YMSprint133SubmissionReadinessIndex.readinessFlags canonicalReceipt)
  ≡ true
canonicalInternalPacketReady = refl

canonicalExternalGovernanceAbsent :
  ReadinessFlags.governanceComplete
    (YMSprint133SubmissionReadinessIndex.readinessFlags canonicalReceipt)
  ≡ false
canonicalExternalGovernanceAbsent = refl

canonicalExternalAcceptanceAbsent :
  ReadinessFlags.acceptancePresent
    (YMSprint133SubmissionReadinessIndex.readinessFlags canonicalReceipt)
  ≡ false
canonicalExternalAcceptanceAbsent = refl

canonicalClayYangMillsNotPromoted :
  ReadinessFlags.clayPromoted
    (YMSprint133SubmissionReadinessIndex.readinessFlags canonicalReceipt)
  ≡ false
canonicalClayYangMillsNotPromoted = refl
