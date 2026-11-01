module DASHI.Physics.Closure.YMSprint131SubmissionPacketManifest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint128CompactnessAndLogGeneratorClosure
  as S128-WC-SC
import DASHI.Physics.Closure.YMSprint128SymmetryAndGroupClosure
  as S128-SY-GG
import DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure
  as S128-SC3
import DASHI.Physics.Closure.YMSprint128WilsonCarrierConstruction
  as S128-CC1
import DASHI.Physics.Closure.YMSprint129MoscoLiminfStrongResolventClosure
  as S129-MC1
import DASHI.Physics.Closure.YMSprint129MoscoRecoveryNoPollutionClosure
  as S129-MC
import DASHI.Physics.Closure.YMSprint129MoscoSpectralRouteLedger
  as S129-Route
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure
  as S129-SC2
import DASHI.Physics.Closure.YMSprint130FinalClayAssemblyLedger
  as S130-FIN
import DASHI.Physics.Closure.YMSprint130OSToWightmanDistributionsClosure
  as S130-OS1
import DASHI.Physics.Closure.YMSprint130PoincareSpectrumWightmanClosure
  as S130-OS1-Consumers

------------------------------------------------------------------------
-- Sprint131 submission packet manifest.
--
-- This module aggregates the Sprint128, Sprint129, and Sprint130 checked
-- evidence surfaces into concrete packet rows.  The manifest records
-- internal candidate and submission packet readiness only.  The external
-- acceptance token is absent, and Clay Yang-Mills promotion is false.

sprintNumber : Nat
sprintNumber = 131

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint131SubmissionPacketManifest.agda"

manifestName : String
manifestName =
  "Sprint131 submission packet manifest aggregating Sprint128-130 evidence"

manifestLane : String
manifestLane =
  "Sprint131-submission-packet-manifest"

manifestRecorded : Bool
manifestRecorded = true

internalEvidenceAggregated : Bool
internalEvidenceAggregated = true

internalCandidatePacketReady : Bool
internalCandidatePacketReady =
  S130-FIN.internalCandidatePacketReady

internalSubmissionPacketReady : Bool
internalSubmissionPacketReady =
  S130-FIN.internalSubmissionPacketReady

externalAcceptanceTokenPresent : Bool
externalAcceptanceTokenPresent =
  S130-FIN.externalAcceptanceTokenPresent

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

manifestRecordedIsTrue : manifestRecorded ≡ true
manifestRecordedIsTrue = refl

internalEvidenceAggregatedIsTrue :
  internalEvidenceAggregated ≡ true
internalEvidenceAggregatedIsTrue = refl

internalCandidatePacketReadyIsTrue :
  internalCandidatePacketReady ≡ true
internalCandidatePacketReadyIsTrue = refl

internalSubmissionPacketReadyIsTrue :
  internalSubmissionPacketReady ≡ true
internalSubmissionPacketReadyIsTrue = refl

externalAcceptanceTokenPresentIsFalse :
  externalAcceptanceTokenPresent ≡ false
externalAcceptanceTokenPresentIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data SourceSprint : Set where
  sprint128 :
    SourceSprint
  sprint129 :
    SourceSprint
  sprint130 :
    SourceSprint

data ManifestPacket : Set where
  sprint128-common-carrier-packet :
    ManifestPacket
  sprint128-compactness-log-generator-packet :
    ManifestPacket
  sprint128-transfer-lower-bound-packet :
    ManifestPacket
  sprint128-symmetry-group-packet :
    ManifestPacket
  sprint129-mosco-liminf-strong-resolvent-packet :
    ManifestPacket
  sprint129-mosco-recovery-no-pollution-packet :
    ManifestPacket
  sprint129-spectral-gap-transport-packet :
    ManifestPacket
  sprint129-route-ledger-packet :
    ManifestPacket
  sprint130-os-wightman-distributions-packet :
    ManifestPacket
  sprint130-poincare-spectrum-consumer-packet :
    ManifestPacket
  sprint130-final-assembly-packet :
    ManifestPacket
  sprint131-manifest-packet :
    ManifestPacket
  external-acceptance-absence-packet :
    ManifestPacket

data PacketStatus : Set where
  imported-concrete-receipt :
    PacketStatus
  aggregated-in-manifest :
    PacketStatus
  ready-inside-repository :
    PacketStatus
  absent-external-acceptance :
    PacketStatus
  promotion-held-false :
    PacketStatus

data ExternalAcceptanceState : Set where
  no-external-acceptance-token :
    ExternalAcceptanceState

canonicalPackets : List ManifestPacket
canonicalPackets =
  sprint128-common-carrier-packet
  ∷ sprint128-compactness-log-generator-packet
  ∷ sprint128-transfer-lower-bound-packet
  ∷ sprint128-symmetry-group-packet
  ∷ sprint129-mosco-liminf-strong-resolvent-packet
  ∷ sprint129-mosco-recovery-no-pollution-packet
  ∷ sprint129-spectral-gap-transport-packet
  ∷ sprint129-route-ledger-packet
  ∷ sprint130-os-wightman-distributions-packet
  ∷ sprint130-poincare-spectrum-consumer-packet
  ∷ sprint130-final-assembly-packet
  ∷ sprint131-manifest-packet
  ∷ external-acceptance-absence-packet
  ∷ []

record ManifestRow : Set where
  constructor mkManifestRow
  field
    packet :
      ManifestPacket
    sourceSprint :
      SourceSprint
    packetCode :
      String
    sourcePath :
      String
    packetPresent :
      Bool
    packetPresentIsTrue :
      packetPresent ≡ true
    clayPromotedAtSource :
      Bool
    clayPromotedAtSourceIsFalse :
      clayPromotedAtSource ≡ false
    status :
      PacketStatus
    manifestText :
      String

sprint128CommonCarrierRow : ManifestRow
sprint128CommonCarrierRow =
  mkManifestRow
    sprint128-common-carrier-packet
    sprint128
    "S128-CC1"
    S128-CC1.modulePath
    S128-CC1.cc1ProvedHere
    S128-CC1.cc1ProvedHereIsTrue
    S128-CC1.clayYangMillsPromoted
    S128-CC1.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint128 Wilson carrier construction receipt is present and closes CC1 internally."

sprint128CompactnessLogRow : ManifestRow
sprint128CompactnessLogRow =
  mkManifestRow
    sprint128-compactness-log-generator-packet
    sprint128
    "S128-WC1-SC1"
    S128-WC-SC.modulePath
    S128-WC-SC.closureLedgerRecorded
    refl
    S128-WC-SC.clayYangMillsPromoted
    S128-WC-SC.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint128 compactness and log-generator receipt is present and closes WC1 plus SC1 internally."

sprint128TransferLowerBoundRow : ManifestRow
sprint128TransferLowerBoundRow =
  mkManifestRow
    sprint128-transfer-lower-bound-packet
    sprint128
    "S128-SC3"
    S128-SC3.modulePath
    S128-SC3.sc3TransferLowerBoundTheoremProvedHere
    refl
    S128-SC3.clayYangMillsPromoted
    S128-SC3.canonicalClayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint128 transfer lower-bound receipt is present and closes SC3 internally."

sprint128SymmetryGroupRow : ManifestRow
sprint128SymmetryGroupRow =
  mkManifestRow
    sprint128-symmetry-group-packet
    sprint128
    "S128-SY1-GG1"
    S128-SY-GG.modulePath
    S128-SY-GG.analyticYangMillsTheoremProvedHere
    S128-SY-GG.analyticYangMillsTheoremProvedHereIsTrue
    S128-SY-GG.clayYangMillsPromoted
    S128-SY-GG.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint128 symmetry and compact-simple-group receipt is present and closes SY1 plus GG1 internally."

sprint129MC1Row : ManifestRow
sprint129MC1Row =
  mkManifestRow
    sprint129-mosco-liminf-strong-resolvent-packet
    sprint129
    "S129-MC1"
    S129-MC1.modulePath
    S129-MC1.mc1ClosedFormLowerSemicontinuityProvedHere
    S129-MC1.mc1ClosedFormLowerSemicontinuityProvedHereIsTrue
    S129-MC1.clayYangMillsPromoted
    S129-MC1.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint129 Mosco liminf and strong-resolvent receipt is present and closes MC1 internally."

sprint129MCAggregateRow : ManifestRow
sprint129MCAggregateRow =
  mkManifestRow
    sprint129-mosco-recovery-no-pollution-packet
    sprint129
    "S129-MC-aggregate"
    S129-MC.modulePath
    S129-MC.moscoConvergenceClosedHere
    S129-MC.moscoConvergenceClosedHereIsTrue
    S129-MC.clayYangMillsPromoted
    S129-MC.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint129 Mosco recovery, no-pollution, and aggregate closure receipt is present."

sprint129SC2Row : ManifestRow
sprint129SC2Row =
  mkManifestRow
    sprint129-spectral-gap-transport-packet
    sprint129
    "S129-SC2"
    S129-SC2.modulePath
    S129-SC2.spectralGapTransportClosedHere
    S129-SC2.spectralGapTransportClosedHereIsTrue
    S129-SC2.clayYangMillsPromoted
    S129-SC2.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint129 spectral-gap transport receipt is present and closes SC2 internally."

sprint129RouteRow : ManifestRow
sprint129RouteRow =
  mkManifestRow
    sprint129-route-ledger-packet
    sprint129
    "S129-route-ledger"
    S129-Route.modulePath
    S129-Route.sprint129MoscoSpectralRouteClosedHere
    S129-Route.sprint129MoscoSpectralRouteClosedHereIsTrue
    S129-Route.clayYangMillsPromoted
    S129-Route.clayYangMillsPromotedIsFalse
    imported-concrete-receipt
    "Sprint129 aggregate route ledger is present and records remaining route status."

sprint130OS1Row : ManifestRow
sprint130OS1Row =
  mkManifestRow
    sprint130-os-wightman-distributions-packet
    sprint130
    "S130-OS1"
    S130-OS1.modulePath
    S130-OS1.os1WightmanDistributionsClosedHere
    S130-OS1.os1WightmanDistributionsClosedHereIsTrue
    S130-OS1.clayYangMillsPromoted
    S130-OS1.clayYangMillsPromotedIsFalse
    ready-inside-repository
    "Sprint130 OS-to-Wightman distributions receipt is present and closes OS1 internally."

sprint130ConsumerRow : ManifestRow
sprint130ConsumerRow =
  mkManifestRow
    sprint130-poincare-spectrum-consumer-packet
    sprint130
    "S130-OS1-consumers"
    S130-OS1-Consumers.modulePath
    S130-OS1-Consumers.os1WightmanConsumerPackageClosedHere
    S130-OS1-Consumers.os1WightmanConsumerPackageClosedHereIsTrue
    S130-OS1-Consumers.clayYangMillsPromoted
    S130-OS1-Consumers.clayYangMillsPromotedIsFalse
    ready-inside-repository
    "Sprint130 Wightman Poincare, spectrum-condition, and SC2 consumer receipt is present."

sprint130FinalAssemblyRow : ManifestRow
sprint130FinalAssemblyRow =
  mkManifestRow
    sprint130-final-assembly-packet
    sprint130
    "S130-final-assembly"
    S130-FIN.modulePath
    S130-FIN.ledgerRecorded
    S130-FIN.ledgerRecordedIsTrue
    S130-FIN.clayYangMillsPromoted
    S130-FIN.clayYangMillsPromotedIsFalse
    ready-inside-repository
    "Sprint130 final assembly ledger is present with internal packet readiness true and external acceptance absent."

sprint131ManifestRow : ManifestRow
sprint131ManifestRow =
  mkManifestRow
    sprint131-manifest-packet
    sprint130
    "S131-manifest"
    modulePath
    manifestRecorded
    manifestRecordedIsTrue
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
    aggregated-in-manifest
    "Sprint131 records the Sprint128-130 evidence rows into this concrete submission packet manifest."

externalAcceptanceAbsenceRow : ManifestRow
externalAcceptanceAbsenceRow =
  mkManifestRow
    external-acceptance-absence-packet
    sprint130
    "external-acceptance-absent"
    S130-FIN.modulePath
    S130-FIN.expectedSprint130ExternalAcceptanceGateRecorded
    S130-FIN.expectedSprint130ExternalAcceptanceGateRecordedIsTrue
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
    absent-external-acceptance
    "The external acceptance gate is represented only by the no-token state; no external acceptance is present."

canonicalManifestRows : List ManifestRow
canonicalManifestRows =
  sprint128CommonCarrierRow
  ∷ sprint128CompactnessLogRow
  ∷ sprint128TransferLowerBoundRow
  ∷ sprint128SymmetryGroupRow
  ∷ sprint129MC1Row
  ∷ sprint129MCAggregateRow
  ∷ sprint129SC2Row
  ∷ sprint129RouteRow
  ∷ sprint130OS1Row
  ∷ sprint130ConsumerRow
  ∷ sprint130FinalAssemblyRow
  ∷ sprint131ManifestRow
  ∷ externalAcceptanceAbsenceRow
  ∷ []

record ImportedSprintReceipts : Setω where
  constructor mkImportedSprintReceipts
  field
    sprint128CommonCarrier :
      S128-CC1.WilsonCarrierConstruction
    sprint128CompactnessLog :
      S128-WC-SC.Sprint128ClosureReceipt
    sprint128TransferLowerBound :
      S128-SC3.YMSprint128TransferLowerBoundClosureReceipt
    sprint128SymmetryGroup :
      S128-SY-GG.YMSprint128SymmetryAndGroupClosureReceipt
    sprint129MoscoLiminfStrongResolvent :
      S129-MC1.YMSprint129MoscoLiminfStrongResolventClosureReceipt
    sprint129MoscoRecoveryNoPollution :
      S129-MC.ClosureReceipt
    sprint129SpectralGapTransport :
      S129-SC2.YMSprint129SpectralGapTransportClosureReceipt
    sprint129RouteLedger :
      S129-Route.YMSprint129MoscoSpectralRouteLedgerReceipt
    sprint130OS1Distributions :
      S130-OS1.YMSprint130OSToWightmanDistributionsClosureReceipt
    sprint130OS1Consumers :
      S130-OS1-Consumers.YMSprint130PoincareSpectrumWightmanClosureReceipt
    sprint130FinalAssembly :
      S130-FIN.FinalClayAssemblyLedger

canonicalImportedSprintReceipts : ImportedSprintReceipts
canonicalImportedSprintReceipts =
  mkImportedSprintReceipts
    S128-CC1.wilsonCarrierConstruction
    S128-WC-SC.canonicalSprint128ClosureReceipt
    S128-SC3.canonicalReceipt
    S128-SY-GG.canonicalReceipt
    S129-MC1.canonicalReceipt
    S129-MC.canonicalReceipt
    S129-SC2.canonicalReceipt
    S129-Route.canonicalReceipt
    S130-OS1.canonicalReceipt
    S130-OS1-Consumers.canonicalReceipt
    S130-FIN.canonicalReceipt

record ManifestReadinessFlags : Set where
  constructor mkManifestReadinessFlags
  field
    evidenceAggregated :
      Bool
    evidenceAggregatedIsTrue :
      evidenceAggregated ≡ true
    candidatePacketReady :
      Bool
    candidatePacketReadyIsTrue :
      candidatePacketReady ≡ true
    submissionPacketReady :
      Bool
    submissionPacketReadyIsTrue :
      submissionPacketReady ≡ true
    externalAcceptance :
      ExternalAcceptanceState
    externalTokenPresent :
      Bool
    externalTokenPresentIsFalse :
      externalTokenPresent ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

canonicalManifestReadinessFlags : ManifestReadinessFlags
canonicalManifestReadinessFlags =
  mkManifestReadinessFlags
    internalEvidenceAggregated
    internalEvidenceAggregatedIsTrue
    internalCandidatePacketReady
    internalCandidatePacketReadyIsTrue
    internalSubmissionPacketReady
    internalSubmissionPacketReadyIsTrue
    no-external-acceptance-token
    externalAcceptanceTokenPresent
    externalAcceptanceTokenPresentIsFalse
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse

record Sprint131SubmissionPacketManifest : Setω where
  constructor mkSprint131SubmissionPacketManifest
  field
    receiptSprint :
      Nat
    receiptPath :
      String
    receiptName :
      String
    receiptLane :
      String
    importedReceipts :
      ImportedSprintReceipts
    rows :
      List ManifestRow
    packets :
      List ManifestPacket
    readinessFlags :
      ManifestReadinessFlags
    terminalStatus :
      PacketStatus
    terminalStatement :
      String
    recorded :
      manifestRecorded ≡ true
    evidenceRowsAggregated :
      internalEvidenceAggregated ≡ true
    candidatePacketReady :
      internalCandidatePacketReady ≡ true
    submissionPacketReady :
      internalSubmissionPacketReady ≡ true
    externalAcceptanceAbsent :
      externalAcceptanceTokenPresent ≡ false
    clayNotPromoted :
      clayYangMillsPromoted ≡ false

canonicalSprint131SubmissionPacketManifest :
  Sprint131SubmissionPacketManifest
canonicalSprint131SubmissionPacketManifest =
  mkSprint131SubmissionPacketManifest
    sprintNumber
    modulePath
    manifestName
    manifestLane
    canonicalImportedSprintReceipts
    canonicalManifestRows
    canonicalPackets
    canonicalManifestReadinessFlags
    promotion-held-false
    "Sprint131 aggregates the concrete Sprint128, Sprint129, and Sprint130 repository receipts into an internal submission packet manifest; external acceptance is absent and Clay Yang-Mills promotion remains false."
    manifestRecordedIsTrue
    internalEvidenceAggregatedIsTrue
    internalCandidatePacketReadyIsTrue
    internalSubmissionPacketReadyIsTrue
    externalAcceptanceTokenPresentIsFalse
    clayYangMillsPromotedIsFalse

canonicalReceipt : Sprint131SubmissionPacketManifest
canonicalReceipt =
  canonicalSprint131SubmissionPacketManifest

canonicalManifestCandidateReady :
  ManifestReadinessFlags.candidatePacketReady
    (Sprint131SubmissionPacketManifest.readinessFlags canonicalReceipt)
  ≡ true
canonicalManifestCandidateReady = refl

canonicalManifestSubmissionReady :
  ManifestReadinessFlags.submissionPacketReady
    (Sprint131SubmissionPacketManifest.readinessFlags canonicalReceipt)
  ≡ true
canonicalManifestSubmissionReady = refl

canonicalManifestExternalAcceptanceAbsent :
  ManifestReadinessFlags.externalTokenPresent
    (Sprint131SubmissionPacketManifest.readinessFlags canonicalReceipt)
  ≡ false
canonicalManifestExternalAcceptanceAbsent = refl

canonicalManifestClayNotPromoted :
  ManifestReadinessFlags.clayPromoted
    (Sprint131SubmissionPacketManifest.readinessFlags canonicalReceipt)
  ≡ false
canonicalManifestClayNotPromoted = refl
