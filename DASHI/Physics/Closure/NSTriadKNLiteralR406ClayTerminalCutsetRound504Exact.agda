module DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact where

------------------------------------------------------------------------
-- ROUND504 / LITERAL R406 CLAY-FACING TERMINAL CUTSET
--
-- R496-R500 construct an exact off-diagonal direct resolvent signed cross on
-- the live R406 remainder carrier. R503 compiles a cutoff-uniform upper bound
-- on that SAME cross to R415. R421 then feeds one R415 payment into the critical
-- barrier, but R414/R421 still require an independent phase-sensitive signed
-- critical-production slice with the literal R406 remainder on its RHS.
--
-- Therefore the strict terminal analytic cutset is TWO-LEAF:
--
--   A. literal R406 signed-cross payment
--      (same-object integrated receipt + cutoff-uniform upper bound);
--
--   B. literal R406 phase-sensitive critical-production slice
--      plus cutoff-uniform initial critical ceiling.
--
-- Full R439 companion equality, Laplace factorization, Cauchy PSD, Schur
-- majorization, and R284 decomposition are not mandatory prerequisites.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossDirectToCriticalBarrierRound421Exact as R421
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNDirectResolventOffDiagonalBoundaryRound502Exact as R502

------------------------------------------------------------------------
-- Two independent terminal coordinates.
------------------------------------------------------------------------

data TerminalResidual : Set where
  missingLiteralR406SignedCrossPayment : TerminalResidual
  missingLiteralR406CriticalProductionSlice : TerminalResidual
  terminalCutsetClosed : TerminalResidual

record TerminalStatus : Set where
  constructor terminal-status
  field
    signedCrossPaymentPresent : Bool
    criticalProductionSlicePresent : Bool

open TerminalStatus public

firstTerminalResidual : TerminalStatus → TerminalResidual
firstTerminalResidual (terminal-status false slice) =
  missingLiteralR406SignedCrossPayment
firstTerminalResidual (terminal-status true false) =
  missingLiteralR406CriticalProductionSlice
firstTerminalResidual (terminal-status true true) = terminalCutsetClosed

data TerminalMechanism : Set where
  ThinkSignedSameScaleSpacetime : TerminalMechanism
  ThinkPhaseSensitiveCriticalProduction : TerminalMechanism
  CompileR421CriticalBarrier : TerminalMechanism

mechanismFor : TerminalResidual → TerminalMechanism
mechanismFor missingLiteralR406SignedCrossPayment =
  ThinkSignedSameScaleSpacetime
mechanismFor missingLiteralR406CriticalProductionSlice =
  ThinkPhaseSensitiveCriticalProduction
mechanismFor terminalCutsetClosed = CompileR421CriticalBarrier

currentTerminalStatus : TerminalStatus
currentTerminalStatus = terminal-status false false

currentFirstTerminalResidual :
  firstTerminalResidual currentTerminalStatus
  ≡ missingLiteralR406SignedCrossPayment
currentFirstTerminalResidual = refl

currentTerminalMechanism :
  mechanismFor (firstTerminalResidual currentTerminalStatus)
  ≡ ThinkSignedSameScaleSpacetime
currentTerminalMechanism = refl

------------------------------------------------------------------------
-- Route classifications.
------------------------------------------------------------------------

directR503Disposition : Least.RouteDisposition
directR503Disposition = Least.admitted

fullR439AsMandatoryDisposition : Least.RouteDisposition
fullR439AsMandatoryDisposition = Least.rejected Least.hypothesisInflation

laplaceAsMandatoryDisposition : Least.RouteDisposition
laplaceAsMandatoryDisposition = Least.rejected Least.hypothesisInflation

r503ExactR415CompilerClosed :
  R503.round503ExactR500ToR415CompilerClosed ≡ true
r503ExactR415CompilerClosed =
  R503.round503ExactR500ToR415CompilerClosedIsTrue

r502FullR439NotSameAsOffDiagonalWithoutReceipt :
  R502.round502OffDiagonalEqualsFullR439WithoutExtraReceipt ≡ false
r502FullR439NotSameAsOffDiagonalWithoutReceipt =
  R502.round502OffDiagonalEqualsFullR439WithoutExtraReceiptIsFalse

r421OnePaymentFeedsBarrier :
  R421.round421OneSignedHeatCrossPaymentFeedsCriticalBarrier ≡ true
r421OnePaymentFeedsBarrier =
  R421.round421OneSignedHeatCrossPaymentFeedsCriticalBarrierIsTrue

r414PhaseSensitiveProductionStillNovel :
  R414.round414RemainingNovelIdentificationIsPhaseSensitiveProductionEstimate
  ≡ true
r414PhaseSensitiveProductionStillNovel = refl

------------------------------------------------------------------------
-- Ledger.
------------------------------------------------------------------------

round504LiteralR406IsCanonicalSameObjectCarrier : Bool
round504LiteralR406IsCanonicalSameObjectCarrier = true

round504TerminalAnalyticLeafCountIsTwo : Bool
round504TerminalAnalyticLeafCountIsTwo = true

round504SignedCrossPaymentClosed : Bool
round504SignedCrossPaymentClosed = false

round504CriticalProductionSliceClosed : Bool
round504CriticalProductionSliceClosed = false

round504FullR439CompanionMandatory : Bool
round504FullR439CompanionMandatory = false

round504LaplaceMandatory : Bool
round504LaplaceMandatory = false

round504ClayPromotion : Bool
round504ClayPromotion = false

round504TerminalAnalyticLeafCountIsTwoIsTrue :
  round504TerminalAnalyticLeafCountIsTwo ≡ true
round504TerminalAnalyticLeafCountIsTwoIsTrue = refl

round504ClayPromotionIsFalse : round504ClayPromotion ≡ false
round504ClayPromotionIsFalse = refl
