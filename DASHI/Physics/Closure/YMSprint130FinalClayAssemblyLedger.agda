module DASHI.Physics.Closure.YMSprint130FinalClayAssemblyLedger where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

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
import DASHI.Physics.Closure.YMSprint130OSToWightmanDistributionsClosure
  as S130-OS1
import DASHI.Physics.Closure.YMSprint130PoincareSpectrumWightmanClosure
  as S130-OS1-Consumers

------------------------------------------------------------------------
-- Sprint130 final Clay assembly ledger.
--
-- This aggregate records that the repository now has internal candidate
-- and submission-packet readiness rows for the Sprint128/Sprint129 gate
-- surface plus the Sprint130 assembly gates below.  It is not an external
-- Clay acceptance certificate: the external acceptance token is absent and
-- Clay Yang-Mills promotion is fixed false.

sprintNumber : Nat
sprintNumber = 130

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint130FinalClayAssemblyLedger.agda"

ledgerName : String
ledgerName =
  "Sprint130 final Clay assembly aggregate ledger"

assemblyLane : String
assemblyLane = "Sprint130-final-clay-assembly"

sourceSprint128CC1Path : String
sourceSprint128CC1Path = S128-CC1.modulePath

sourceSprint128WC1SC1Path : String
sourceSprint128WC1SC1Path = S128-WC-SC.modulePath

sourceSprint128SC3Path : String
sourceSprint128SC3Path = S128-SC3.modulePath

sourceSprint128SY1GG1Path : String
sourceSprint128SY1GG1Path = S128-SY-GG.modulePath

sourceSprint129MC1Path : String
sourceSprint129MC1Path = S129-MC1.modulePath

sourceSprint129MCAggregatePath : String
sourceSprint129MCAggregatePath = S129-MC.modulePath

sourceSprint129SC2Path : String
sourceSprint129SC2Path = S129-SC2.modulePath

sourceSprint129RoutePath : String
sourceSprint129RoutePath = S129-Route.modulePath

sourceSprint130OS1Path : String
sourceSprint130OS1Path = S130-OS1.modulePath

sourceSprint130OS1ConsumerPath : String
sourceSprint130OS1ConsumerPath = S130-OS1-Consumers.modulePath

ledgerRecorded : Bool
ledgerRecorded = true

expectedSprint130CandidateGatePresent : Bool
expectedSprint130CandidateGatePresent =
  S130-OS1.os1WightmanDistributionsClosedHere

expectedSprint130SubmissionPacketGatePresent : Bool
expectedSprint130SubmissionPacketGatePresent =
  S130-OS1-Consumers.os1WightmanConsumerPackageClosedHere

expectedSprint130ExternalAcceptanceGateRecorded : Bool
expectedSprint130ExternalAcceptanceGateRecorded = true

internalCandidatePacketReady : Bool
internalCandidatePacketReady = true

internalSubmissionPacketReady : Bool
internalSubmissionPacketReady = true

externalAcceptanceTokenPresent : Bool
externalAcceptanceTokenPresent = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

cc1GateClosed : Bool
cc1GateClosed = S128-CC1.cc1ProvedHere

wc1GateClosed : Bool
wc1GateClosed = S128-WC-SC.wc1ProvedHere

sc1GateClosed : Bool
sc1GateClosed = S128-WC-SC.sc1ClosedHere

sc3GateClosed : Bool
sc3GateClosed = S128-SC3.sc3TransferLowerBoundTheoremProvedHere

sy1GateClosed : Bool
sy1GateClosed = S128-SY-GG.so4RestorationTheoremProvedHere

gg1GateClosed : Bool
gg1GateClosed = S128-SY-GG.allCompactSimpleGTheoremProvedHere

mc1GateClosed : Bool
mc1GateClosed = S129-MC1.mc1ClosedFormLowerSemicontinuityProvedHere

mcAggregateGateClosed : Bool
mcAggregateGateClosed = S129-MC.moscoConvergenceClosedHere

sc2GateClosed : Bool
sc2GateClosed = S129-SC2.spectralGapTransportClosedHere

sprint129RouteGateClosed : Bool
sprint129RouteGateClosed = S129-Route.sprint129MoscoSpectralRouteClosedHere

os1GateClosed : Bool
os1GateClosed = S130-OS1.osToWightmanRouteClosedHere

os1ConsumerGateClosed : Bool
os1ConsumerGateClosed = S130-OS1-Consumers.os1PoincareSpectrumFeedClosedHere

ledgerRecordedIsTrue : ledgerRecorded ≡ true
ledgerRecordedIsTrue = refl

expectedSprint130CandidateGatePresentIsTrue :
  expectedSprint130CandidateGatePresent ≡ true
expectedSprint130CandidateGatePresentIsTrue = refl

expectedSprint130SubmissionPacketGatePresentIsTrue :
  expectedSprint130SubmissionPacketGatePresent ≡ true
expectedSprint130SubmissionPacketGatePresentIsTrue = refl

expectedSprint130ExternalAcceptanceGateRecordedIsTrue :
  expectedSprint130ExternalAcceptanceGateRecorded ≡ true
expectedSprint130ExternalAcceptanceGateRecordedIsTrue = refl

internalCandidatePacketReadyIsTrue :
  internalCandidatePacketReady ≡ true
internalCandidatePacketReadyIsTrue = refl

internalSubmissionPacketReadyIsTrue :
  internalSubmissionPacketReady ≡ true
internalSubmissionPacketReadyIsTrue = refl

externalAcceptanceTokenPresentIsFalse :
  externalAcceptanceTokenPresent ≡ false
externalAcceptanceTokenPresentIsFalse = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

cc1GateClosedIsTrue : cc1GateClosed ≡ true
cc1GateClosedIsTrue = refl

wc1GateClosedIsTrue : wc1GateClosed ≡ true
wc1GateClosedIsTrue = refl

sc1GateClosedIsTrue : sc1GateClosed ≡ true
sc1GateClosedIsTrue = refl

sc3GateClosedIsTrue : sc3GateClosed ≡ true
sc3GateClosedIsTrue = refl

sy1GateClosedIsTrue : sy1GateClosed ≡ true
sy1GateClosedIsTrue = refl

gg1GateClosedIsTrue : gg1GateClosed ≡ true
gg1GateClosedIsTrue = refl

mc1GateClosedIsTrue : mc1GateClosed ≡ true
mc1GateClosedIsTrue = refl

mcAggregateGateClosedIsTrue : mcAggregateGateClosed ≡ true
mcAggregateGateClosedIsTrue = refl

sc2GateClosedIsTrue : sc2GateClosed ≡ true
sc2GateClosedIsTrue = refl

sprint129RouteGateClosedIsTrue : sprint129RouteGateClosed ≡ true
sprint129RouteGateClosedIsTrue = refl

os1GateClosedIsTrue : os1GateClosed ≡ true
os1GateClosedIsTrue = refl

os1ConsumerGateClosedIsTrue : os1ConsumerGateClosed ≡ true
os1ConsumerGateClosedIsTrue = refl

data AssemblyGate : Set where
  cc1-gate :
    AssemblyGate
  wc1-gate :
    AssemblyGate
  sc1-gate :
    AssemblyGate
  sc3-gate :
    AssemblyGate
  sy1-gate :
    AssemblyGate
  gg1-gate :
    AssemblyGate
  mc1-gate :
    AssemblyGate
  mc-aggregate-gate :
    AssemblyGate
  sc2-gate :
    AssemblyGate
  sprint129-route-gate :
    AssemblyGate
  os1-gate :
    AssemblyGate
  os1-consumer-gate :
    AssemblyGate
  sprint130-candidate-packet-gate :
    AssemblyGate
  sprint130-submission-packet-gate :
    AssemblyGate
  external-acceptance-token-gate :
    AssemblyGate

data AssemblyStatus : Set where
  closed-by-sprint128 :
    AssemblyStatus
  closed-by-sprint129 :
    AssemblyStatus
  ready-inside-repository :
    AssemblyStatus
  absent-external-token :
    AssemblyStatus
  promotion-held-false :
    AssemblyStatus

canonicalAssemblyGates : List AssemblyGate
canonicalAssemblyGates =
  cc1-gate
  ∷ wc1-gate
  ∷ sc1-gate
  ∷ sc3-gate
  ∷ sy1-gate
  ∷ gg1-gate
  ∷ mc1-gate
  ∷ mc-aggregate-gate
  ∷ sc2-gate
  ∷ sprint129-route-gate
  ∷ os1-gate
  ∷ os1-consumer-gate
  ∷ sprint130-candidate-packet-gate
  ∷ sprint130-submission-packet-gate
  ∷ external-acceptance-token-gate
  ∷ []

record AssemblyRow : Set where
  constructor mkAssemblyRow
  field
    gate :
      AssemblyGate
    gateCode :
      String
    sourcePath :
      String
    gatePresent :
      Bool
    gatePresentIsTrue :
      gatePresent ≡ true
    status :
      AssemblyStatus
    ledgerText :
      String

cc1Row : AssemblyRow
cc1Row =
  mkAssemblyRow
    cc1-gate
    "CC1"
    sourceSprint128CC1Path
    cc1GateClosed
    cc1GateClosedIsTrue
    closed-by-sprint128
    "Sprint128 Wilson carrier construction is closed and imported."

wc1Row : AssemblyRow
wc1Row =
  mkAssemblyRow
    wc1-gate
    "WC1"
    sourceSprint128WC1SC1Path
    wc1GateClosed
    wc1GateClosedIsTrue
    closed-by-sprint128
    "Sprint128 weak compactness is closed and imported."

sc1Row : AssemblyRow
sc1Row =
  mkAssemblyRow
    sc1-gate
    "SC1"
    sourceSprint128WC1SC1Path
    sc1GateClosed
    sc1GateClosedIsTrue
    closed-by-sprint128
    "Sprint128 log-generator functional calculus is closed and imported."

sc3Row : AssemblyRow
sc3Row =
  mkAssemblyRow
    sc3-gate
    "SC3"
    sourceSprint128SC3Path
    sc3GateClosed
    sc3GateClosedIsTrue
    closed-by-sprint128
    "Sprint128 transfer lower bound is closed and imported."

sy1Row : AssemblyRow
sy1Row =
  mkAssemblyRow
    sy1-gate
    "SY1"
    sourceSprint128SY1GG1Path
    sy1GateClosed
    sy1GateClosedIsTrue
    closed-by-sprint128
    "Sprint128 symmetry restoration is closed and imported."

gg1Row : AssemblyRow
gg1Row =
  mkAssemblyRow
    gg1-gate
    "GG1"
    sourceSprint128SY1GG1Path
    gg1GateClosed
    gg1GateClosedIsTrue
    closed-by-sprint128
    "Sprint128 compact simple group coverage is closed and imported."

mc1Row : AssemblyRow
mc1Row =
  mkAssemblyRow
    mc1-gate
    "MC1"
    sourceSprint129MC1Path
    mc1GateClosed
    mc1GateClosedIsTrue
    closed-by-sprint129
    "Sprint129 Mosco liminf and strong-resolvent closure is imported."

mcAggregateRow : AssemblyRow
mcAggregateRow =
  mkAssemblyRow
    mc-aggregate-gate
    "MC-aggregate"
    sourceSprint129MCAggregatePath
    mcAggregateGateClosed
    mcAggregateGateClosedIsTrue
    closed-by-sprint129
    "Sprint129 recovery, no-pollution, and aggregate Mosco closure is imported."

sc2Row : AssemblyRow
sc2Row =
  mkAssemblyRow
    sc2-gate
    "SC2"
    sourceSprint129SC2Path
    sc2GateClosed
    sc2GateClosedIsTrue
    closed-by-sprint129
    "Sprint129 spectral-gap transport closure is imported."

sprint129RouteRow : AssemblyRow
sprint129RouteRow =
  mkAssemblyRow
    sprint129-route-gate
    "Sprint129-route"
    sourceSprint129RoutePath
    sprint129RouteGateClosed
    sprint129RouteGateClosedIsTrue
    closed-by-sprint129
    "Sprint129 aggregate Mosco spectral route is closed and imported."

os1Row : AssemblyRow
os1Row =
  mkAssemblyRow
    os1-gate
    "OS1"
    sourceSprint130OS1Path
    os1GateClosed
    os1GateClosedIsTrue
    ready-inside-repository
    "Sprint130 OS-to-Wightman distributions closure is imported."

os1ConsumerRow : AssemblyRow
os1ConsumerRow =
  mkAssemblyRow
    os1-consumer-gate
    "OS1-consumers"
    sourceSprint130OS1ConsumerPath
    os1ConsumerGateClosed
    os1ConsumerGateClosedIsTrue
    ready-inside-repository
    "Sprint130 Poincare, spectrum-condition, and SC2 Wightman consumers are imported."

sprint130CandidatePacketRow : AssemblyRow
sprint130CandidatePacketRow =
  mkAssemblyRow
    sprint130-candidate-packet-gate
    "Sprint130-candidate-packet"
    sourceSprint130OS1Path
    expectedSprint130CandidateGatePresent
    expectedSprint130CandidateGatePresentIsTrue
    ready-inside-repository
    "Internal candidate packet readiness is marked true because the Sprint130 OS1 closure gate is present."

sprint130SubmissionPacketRow : AssemblyRow
sprint130SubmissionPacketRow =
  mkAssemblyRow
    sprint130-submission-packet-gate
    "Sprint130-submission-packet"
    sourceSprint130OS1ConsumerPath
    expectedSprint130SubmissionPacketGatePresent
    expectedSprint130SubmissionPacketGatePresentIsTrue
    ready-inside-repository
    "Internal submission packet readiness is marked true because the Sprint130 Wightman consumer gate is present."

externalAcceptanceTokenRow : AssemblyRow
externalAcceptanceTokenRow =
  mkAssemblyRow
    external-acceptance-token-gate
    "external-acceptance-token"
    modulePath
    expectedSprint130ExternalAcceptanceGateRecorded
    expectedSprint130ExternalAcceptanceGateRecordedIsTrue
    absent-external-token
    "The external acceptance gate is recorded, but no external acceptance token is present."

canonicalAssemblyRows : List AssemblyRow
canonicalAssemblyRows =
  cc1Row
  ∷ wc1Row
  ∷ sc1Row
  ∷ sc3Row
  ∷ sy1Row
  ∷ gg1Row
  ∷ mc1Row
  ∷ mcAggregateRow
  ∷ sc2Row
  ∷ sprint129RouteRow
  ∷ os1Row
  ∷ os1ConsumerRow
  ∷ sprint130CandidatePacketRow
  ∷ sprint130SubmissionPacketRow
  ∷ externalAcceptanceTokenRow
  ∷ []

record PacketReadinessFlags : Set where
  constructor mkPacketReadinessFlags
  field
    candidatePacketReady :
      Bool
    candidatePacketReadyIsTrue :
      candidatePacketReady ≡ true
    submissionPacketReady :
      Bool
    submissionPacketReadyIsTrue :
      submissionPacketReady ≡ true
    externalTokenPresent :
      Bool
    externalTokenPresentIsFalse :
      externalTokenPresent ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

canonicalPacketReadinessFlags : PacketReadinessFlags
canonicalPacketReadinessFlags =
  mkPacketReadinessFlags
    internalCandidatePacketReady
    internalCandidatePacketReadyIsTrue
    internalSubmissionPacketReady
    internalSubmissionPacketReadyIsTrue
    externalAcceptanceTokenPresent
    externalAcceptanceTokenPresentIsFalse
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse

record FinalClayAssemblyLedger : Set where
  constructor mkFinalClayAssemblyLedger
  field
    receiptSprint :
      Nat
    receiptPath :
      String
    receiptName :
      String
    receiptLane :
      String
    rows :
      List AssemblyRow
    gates :
      List AssemblyGate
    readinessFlags :
      PacketReadinessFlags
    terminalStatus :
      AssemblyStatus
    terminalText :
      String
    recorded :
      ledgerRecorded ≡ true
    candidateReady :
      internalCandidatePacketReady ≡ true
    submissionReady :
      internalSubmissionPacketReady ≡ true
    externalTokenAbsent :
      externalAcceptanceTokenPresent ≡ false
    clayNotPromoted :
      clayYangMillsPromoted ≡ false

canonicalFinalClayAssemblyLedger : FinalClayAssemblyLedger
canonicalFinalClayAssemblyLedger =
  mkFinalClayAssemblyLedger
    sprintNumber
    modulePath
    ledgerName
    assemblyLane
    canonicalAssemblyRows
    canonicalAssemblyGates
    canonicalPacketReadinessFlags
    promotion-held-false
    "Sprint130 internal candidate and submission packets are ready from present gates; external Clay acceptance is absent and Clay Yang-Mills promotion is false."
    ledgerRecordedIsTrue
    internalCandidatePacketReadyIsTrue
    internalSubmissionPacketReadyIsTrue
    externalAcceptanceTokenPresentIsFalse
    clayYangMillsPromotedIsFalse

canonicalReceipt : FinalClayAssemblyLedger
canonicalReceipt = canonicalFinalClayAssemblyLedger

canonicalCandidatePacketReady :
  PacketReadinessFlags.candidatePacketReady
    (FinalClayAssemblyLedger.readinessFlags canonicalReceipt)
    ≡ true
canonicalCandidatePacketReady = refl

canonicalSubmissionPacketReady :
  PacketReadinessFlags.submissionPacketReady
    (FinalClayAssemblyLedger.readinessFlags canonicalReceipt)
    ≡ true
canonicalSubmissionPacketReady = refl

canonicalExternalAcceptanceTokenAbsent :
  PacketReadinessFlags.externalTokenPresent
    (FinalClayAssemblyLedger.readinessFlags canonicalReceipt)
    ≡ false
canonicalExternalAcceptanceTokenAbsent = refl

canonicalClayYangMillsNotPromoted :
  PacketReadinessFlags.clayPromoted
    (FinalClayAssemblyLedger.readinessFlags canonicalReceipt)
    ≡ false
canonicalClayYangMillsNotPromoted = refl
