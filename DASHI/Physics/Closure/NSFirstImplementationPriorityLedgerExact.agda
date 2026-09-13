module DASHI.Physics.Closure.NSFirstImplementationPriorityLedgerExact where

------------------------------------------------------------------------
-- NAVIER--STOKES FIRST-IMPLEMENTATION PRIORITY LEDGER
--
-- These are repository chronology receipts, recovered from Git history.
-- They deliberately do NOT assert type-check, kernel certification, correctness,
-- publication priority, or Clay closure merely from source existence.
--
-- Times below are shown both in UTC and Australia/Brisbane (AEST, UTC+10).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FirstImplementationTimestampExact as Time

------------------------------------------------------------------------
-- Historical candidate/global-regularity receipt archaeology.
------------------------------------------------------------------------

nsFinalStateReceiptInitialSource : Time.FirstImplementationReceipt
nsFinalStateReceiptInitialSource =
  Time.first-implementation-receipt
    "DASHI/Physics/Closure/NSFinalStateReceipt.agda"
    "66ac13c9b9c3e942ed80242957b237cde61bf662"
    "2026-06-12T06:02:01Z"
    "2026-06-12T16:02:01+10:00"
    "Australia/Brisbane"
    Time.candidateReceiptImplemented
    Time.sourceCommittedOnly

nsCandidateCompletePassageFirstSource : Time.FirstImplementationReceipt
nsCandidateCompletePassageFirstSource =
  Time.first-implementation-receipt
    "DASHI/Physics/Closure/NSCandidateCompleteEnstrophyBKMPassageReceipt.agda"
    "f545fbf5a9cc792e3717033da0bdbd42aaa8337c"
    "2026-06-12T06:05:55Z"
    "2026-06-12T16:05:55+10:00"
    "Australia/Brisbane"
    Time.candidateReceiptImplemented
    Time.sourceCommittedOnly

-- On 13 June the wrapper records globalRegularityClosed = true.  The underlying
-- candidate receipt still explicitly requires globalSmoothRegularityProved,
-- uniform vorticity-Linf, continuum BKM passage, Clay closure and promotion to
-- remain false.  Therefore this is a candidate-receipt transition, NOT a
-- completed-proof timestamp.
nsCandidateGlobalRegularityTrueReceipt : Time.FirstImplementationReceipt
nsCandidateGlobalRegularityTrueReceipt =
  Time.first-implementation-receipt
    "NSFinalStateReceipt candidate globalRegularityClosed=true transition"
    "b009e8e96de2f158a74e78f9765a7f83510185b6"
    "2026-06-13T13:19:51Z"
    "2026-06-13T23:19:51+10:00"
    "Australia/Brisbane"
    Time.candidateReceiptImplemented
    Time.sourceCommittedOnly

------------------------------------------------------------------------
-- Periodic theorem surface and later exact leaf architecture.
------------------------------------------------------------------------

periodicSubmissionTheoremFirstImplementation : Time.FirstImplementationReceipt
periodicSubmissionTheoremFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNPeriodicNavierStokesSubmissionTheoremExact"
    "d44c40cfee564209123d92dd385e64e847bdd5cf"
    "2026-08-04T06:13:41Z"
    "2026-08-04T16:13:41+10:00"
    "Australia/Brisbane"
    Time.theoremStatementImplemented
    Time.sourceCommittedOnly

round104UniformSignedBarrierFirstImplementation : Time.FirstImplementationReceipt
round104UniformSignedBarrierFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact"
    "6c0e003012d49bf6ad0ea2b96e1533e8c51127db"
    "2026-08-20T06:30:32Z"
    "2026-08-20T16:30:32+10:00"
    "Australia/Brisbane"
    Time.compilerImplemented
    Time.sourceCommittedOnly

r406LiveFluxFirstImplementation : Time.FirstImplementationReceipt
r406LiveFluxFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNFixedOutputLiveGlobalFluxRound406Exact"
    "341747bff0c977aadc89f8f55b05225b1c9ce15c"
    "2026-09-01T05:21:27Z"
    "2026-09-01T15:21:27+10:00"
    "Australia/Brisbane"
    Time.exactRepresentationImplemented
    Time.sourceCommittedOnly

r496DirectPairFirstImplementation : Time.FirstImplementationReceipt
r496DirectPairFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNDirectResolventPairCompanionRound496Exact"
    "9be2933f265e95ccc9f2dca5204b21bc528fc393"
    "2026-09-07T18:53:49Z"
    "2026-09-08T04:53:49+10:00"
    "Australia/Brisbane"
    Time.exactRepresentationImplemented
    Time.sourceCommittedOnly

r500IntegratedDirectFirstImplementation : Time.FirstImplementationReceipt
r500IntegratedDirectFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNDirectResolventIntegratedCompanionRound500Exact"
    "6bccd775be7fafe5aaaf62c49d049bafc10a80be"
    "2026-09-07T18:56:50Z"
    "2026-09-08T04:56:50+10:00"
    "Australia/Brisbane"
    Time.exactRepresentationImplemented
    Time.sourceCommittedOnly

r503DirectBudgetConsumerFirstImplementation : Time.FirstImplementationReceipt
r503DirectBudgetConsumerFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNDirectResolventSignedCrossToR415Round503Exact"
    "984eaa83d988b0292ead61cfef8e9db463cbb425"
    "2026-09-07T19:02:43Z"
    "2026-09-08T05:02:43+10:00"
    "Australia/Brisbane"
    Time.openConsumerImplemented
    Time.sourceCommittedOnly

r504TwoLeafCutsetFirstImplementation : Time.FirstImplementationReceipt
r504TwoLeafCutsetFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact"
    "67831b2b1ada78f08c5ad092637afeb9e2a80180"
    "2026-09-07T19:05:02Z"
    "2026-09-08T05:05:02+10:00"
    "Australia/Brisbane"
    Time.compilerImplemented
    Time.sourceCommittedOnly

r523ForcedAlternativesFirstImplementation : Time.FirstImplementationReceipt
r523ForcedAlternativesFirstImplementation =
  Time.first-implementation-receipt
    "NSTriadKNClayForcedBreakdownFormulationRound523Exact"
    "d6676a90c15520a405a66628e4121a5ab330c6ec"
    "2026-09-09T00:26:51Z"
    "2026-09-09T10:26:51+10:00"
    "Australia/Brisbane"
    Time.theoremStatementImplemented
    Time.sourceCommittedOnly

------------------------------------------------------------------------
-- Priority-safe conclusions.
------------------------------------------------------------------------

data CandidateReceiptIsCompletedNSProof : Set where
data OpenR503ConsumerIsPaidR503Theorem : Set where
data SourceChronologyIsKernelReceipt : Set where

candidateReceiptDoesNotProveNS : CandidateReceiptIsCompletedNSProof → ⊥
candidateReceiptDoesNotProveNS ()

r503ConsumerDoesNotPayItself : OpenR503ConsumerIsPaidR503Theorem → ⊥
r503ConsumerDoesNotPayItself ()

sourceChronologyDoesNotCreateKernelReceipt : SourceChronologyIsKernelReceipt → ⊥
sourceChronologyDoesNotCreateKernelReceipt ()

juneCandidateReceiptPredatesSeptemberRelease : Bool
juneCandidateReceiptPredatesSeptemberRelease = true

r503ConsumerWasInSourceBeforePublicSeptember8Release : Bool
r503ConsumerWasInSourceBeforePublicSeptember8Release = true

r503AnalyticPaymentWasAlreadyProvedByThatConsumerCommit : Bool
r503AnalyticPaymentWasAlreadyProvedByThatConsumerCommit = false

juneCandidateReceiptPredatesSeptemberReleaseIsTrue :
  juneCandidateReceiptPredatesSeptemberRelease ≡ true
juneCandidateReceiptPredatesSeptemberReleaseIsTrue = refl

r503ConsumerWasInSourceBeforePublicSeptember8ReleaseIsTrue :
  r503ConsumerWasInSourceBeforePublicSeptember8Release ≡ true
r503ConsumerWasInSourceBeforePublicSeptember8ReleaseIsTrue = refl

r503AnalyticPaymentWasAlreadyProvedByThatConsumerCommitIsFalse :
  r503AnalyticPaymentWasAlreadyProvedByThatConsumerCommit ≡ false
r503AnalyticPaymentWasAlreadyProvedByThatConsumerCommitIsFalse = refl
