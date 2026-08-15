module DASHI.Papers.NavierStokes.TheoremInterface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6TheoremLadderBoundary as A6
import DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary as A6Bony
import DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary as A7
import DASHI.Physics.Closure.NSA8FullLocalDefectMonotonicityBoundary as A8
import DASHI.Physics.Closure.NSA9CKNBKMClosureBoundary as A9
import DASHI.Physics.Closure.NSFinalStateReceipt as Final
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound47Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound50Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound51Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound52Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound53Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound54Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound55Exact
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact
import DASHI.Physics.Closure.NSTriadKNFixedShiftScaleMatchedCapacityRound60Exact
import DASHI.Papers.NavierStokes.ClayContractRound23 as Clay23

------------------------------------------------------------------------
-- Paper-facing Navier-Stokes theorem/status interface.
--
-- This module is a thin, non-promoting wrapper over the current closure
-- receipts. It intentionally exports theorem-status fields suitable for a
-- paper spine while preserving the Clay terminal boundary as false. Round 23
-- carries the literal Fefferman periodic contract as a canonical fail-closed
-- surface: the target theorem type is represented, but physical producers and
-- unconditional promotion remain false.
--
-- Round55 imports the six A--F cutset modules. Round59/60 then sharpen the
-- quantitative A--C boundaries without changing any physical promotion bit:
--
-- * A: one canonical time-dependent Duhamel source plus estimates indexed by
--   that source definitionally constructs the transfer; a separately supplied
--   transfer/same-object equality is no longer accepted.
-- * B: active same/adjacent normalized odd-(P/Q) Gram bounds extend through
--   exact off-support annihilation to the literal whole-fibre inequality
--   17/64 + 2(65/512) = 133/256.
-- * C: scale-matched bounds X_n <= K C r^n and A_n <= a C r^n together with
--   a + B_* K <= r-q construct the uniform division-free product capacity.
--
-- The terminal Clay bit remains false: the literal A trajectory/estimates, B
-- active numerical estimates, and C scale-matched physical bounds are not
-- manufactured by these reductions.

paperInterfaceStatement : String
paperInterfaceStatement =
  "Paper-facing NS interface: A6/A7/A8/A9 closure receipts, Round-47/50/51/52/53/54/55 highest-alpha aggregates, and the literal Round 23 Fefferman periodic contract are imported; Round59/60 sharpen A-C to one canonical Duhamel source, the literal 133/256 Com whole-fibre endpoint, and a scale-matched division-free fixed-shift capacity theorem, while unresolved physical producer inhabitation, Clay Navier-Stokes and terminal promotion remain false."

record NSPaperTheoremStatus : Setω where
  field
    a6TheoremLadderReceipt :
      A6.NSA6TheoremLadderBoundary
    a6TheoremLadderReceiptIsCanonical :
      a6TheoremLadderReceipt ≡ A6.canonicalNSA6TheoremLadderBoundary

    a6BonyRepairReceipt :
      A6Bony.NSBonyParaproductA6RepairBoundary
    a6BonyRepairReceiptIsCanonical :
      a6BonyRepairReceipt
        ≡ A6Bony.canonicalNSBonyParaproductA6RepairBoundary

    a7ResidualDepletionReceipt :
      A7.NSA7ResidualDepletionGronwallBoundary
    a7ResidualDepletionReceiptIsCanonical :
      a7ResidualDepletionReceipt
        ≡ A7.canonicalNSA7ResidualDepletionGronwallBoundary

    a8LocalDefectReceipt :
      A8.NSA8FullLocalDefectMonotonicityBoundary
    a8LocalDefectReceiptIsCanonical :
      a8LocalDefectReceipt
        ≡ A8.canonicalNSA8FullLocalDefectMonotonicityBoundary

    a9CKNBKMReceipt :
      A9.NSA9CKNBKMClosureBoundary
    a9CKNBKMReceiptIsCanonical :
      a9CKNBKMReceipt
        ≡ A9.canonicalNSA9CKNBKMClosureBoundary

    clayContractRound23 :
      Clay23.NSClayContractRound23Status
    clayContractRound23IsCanonical :
      clayContractRound23 ≡ Clay23.canonicalNSClayContractRound23Status
    clayLiteralTargetImplemented :
      Clay23.literalFeffermanPeriodicStatementImplemented clayContractRound23
      ≡ true
    clayPhysicalProducersStillOpen :
      Clay23.physicalProducersInhabited clayContractRound23 ≡ false
    clayRound23PromotionStillFalse :
      Clay23.unconditionalClayTheoremPromoted clayContractRound23 ≡ false

    finalStateReceipt :
      Final.NSFinalStateReceipt
    finalStateStatementIsCanonical :
      Final.statement finalStateReceipt ≡ Final.nsFinalStateStatement

    a6TheoremProved : Bool
    a6TheoremProvedMatchesReceipt :
      a6TheoremProved ≡ A6.A6TheoremProved
    a6TheoremProvedIsTrue :
      a6TheoremProved ≡ true

    a6ResidualNonpositiveProved : Bool
    a6ResidualNonpositiveMatchesReceipt :
      a6ResidualNonpositiveProved ≡ A6.residualNonpositiveProved
    a6ResidualNonpositiveIsTrue :
      a6ResidualNonpositiveProved ≡ true

    a6LocalDefectMonotonicityStillFalse :
      A6.localDefectMonotonicityProved ≡ false
    a6CKNBKMClosureStillFalse :
      A6.cknBkmClosureProved ≡ false
    a6ClayStillFalse :
      A6.nsClayPromoted ≡ false
    a6TerminalStillFalse :
      A6.terminalPromotion ≡ false

    a6BonyRepairPromoted :
      A6Bony.bonyParaproductA6RepairPromotedHere ≡ true
    a6BonyClayStillFalse :
      A6Bony.NSClayNotPromoted ≡ true
    a6BonyTerminalStillFalse :
      A6Bony.terminalPromotionNotPromoted ≡ true

    a7ResidualDepletionProved :
      A7.A7ResidualDepletionGronwallProved ≡ true
    a7ClayStillFalse :
      A7.NSClayPromotedFromA7 ≡ false
    a7TerminalStillFalse :
      A7.TerminalPromotionFromA7 ≡ false

    a8FullLocalDefectMonotonicityProved :
      A8.A8FullLocalDefectMonotonicityProved ≡ true
    a8ClayStillFalse :
      A8.NSClayPromotedFromA8 ≡ false
    a8TerminalStillFalse :
      A8.TerminalPromotionFromA8 ≡ false

    a9CKNBKMClosureProved :
      A9.A9CKNBKMClosureProved ≡ true
    a9ClayStillFalse :
      A9.NSClayPromotedFromA9 ≡ false
    a9TerminalStillFalse :
      A9.TerminalPromotionFromA9 ≡ false

    finalClayStillFalse :
      Final.clayNavierStokesPromoted finalStateReceipt ≡ false
    finalTerminalStillFalse :
      Final.terminalClaimPromoted finalStateReceipt ≡ false

    clayTerminalPromotion : Bool
    clayTerminalPromotionMatchesFinal :
      clayTerminalPromotion
        ≡ Final.terminalClaimPromoted finalStateReceipt
    clayTerminalPromotionIsFalse :
      clayTerminalPromotion ≡ false

    statement : String
    statementIsCanonical :
      statement ≡ paperInterfaceStatement

open NSPaperTheoremStatus public

canonicalNSPaperTheoremStatus : NSPaperTheoremStatus
canonicalNSPaperTheoremStatus =
  record
    { a6TheoremLadderReceipt = A6.canonicalNSA6TheoremLadderBoundary
    ; a6TheoremLadderReceiptIsCanonical = refl
    ; a6BonyRepairReceipt = A6Bony.canonicalNSBonyParaproductA6RepairBoundary
    ; a6BonyRepairReceiptIsCanonical = refl
    ; a7ResidualDepletionReceipt = A7.canonicalNSA7ResidualDepletionGronwallBoundary
    ; a7ResidualDepletionReceiptIsCanonical = refl
    ; a8LocalDefectReceipt = A8.canonicalNSA8FullLocalDefectMonotonicityBoundary
    ; a8LocalDefectReceiptIsCanonical = refl
    ; a9CKNBKMReceipt = A9.canonicalNSA9CKNBKMClosureBoundary
    ; a9CKNBKMReceiptIsCanonical = refl
    ; clayContractRound23 = Clay23.canonicalNSClayContractRound23Status
    ; clayContractRound23IsCanonical = refl
    ; clayLiteralTargetImplemented = Clay23.literalTargetIsImplemented
    ; clayPhysicalProducersStillOpen = Clay23.physicalProducersRemainOpen
    ; clayRound23PromotionStillFalse = Clay23.clayPromotionRemainsFalse
    ; finalStateReceipt = Final.canonicalNSFinalStateReceipt
    ; finalStateStatementIsCanonical = refl
    ; a6TheoremProved = A6.A6TheoremProved
    ; a6TheoremProvedMatchesReceipt = refl
    ; a6TheoremProvedIsTrue = refl
    ; a6ResidualNonpositiveProved = A6.residualNonpositiveProved
    ; a6ResidualNonpositiveMatchesReceipt = refl
    ; a6ResidualNonpositiveIsTrue = refl
    ; a6LocalDefectMonotonicityStillFalse = refl
    ; a6CKNBKMClosureStillFalse = refl
    ; a6ClayStillFalse = refl
    ; a6TerminalStillFalse = refl
    ; a6BonyRepairPromoted = refl
    ; a6BonyClayStillFalse = refl
    ; a6BonyTerminalStillFalse = refl
    ; a7ResidualDepletionProved = A7.A7ResidualDepletionGronwallProvedIsTrue
    ; a7ClayStillFalse = A7.NSClayPromotedFromA7IsFalse
    ; a7TerminalStillFalse = A7.TerminalPromotionFromA7IsFalse
    ; a8FullLocalDefectMonotonicityProved = A8.A8FullLocalDefectMonotonicityProvedIsTrue
    ; a8ClayStillFalse = A8.NSClayPromotedFromA8IsFalse
    ; a8TerminalStillFalse = A8.TerminalPromotionFromA8IsFalse
    ; a9CKNBKMClosureProved = A9.A9CKNBKMClosureProvedIsTrue
    ; a9ClayStillFalse = A9.NSClayPromotedFromA9IsFalse
    ; a9TerminalStillFalse = A9.TerminalPromotionFromA9IsFalse
    ; finalClayStillFalse = refl
    ; finalTerminalStillFalse = refl
    ; clayTerminalPromotion = Final.terminalClaimPromoted Final.canonicalNSFinalStateReceipt
    ; clayTerminalPromotionMatchesFinal = refl
    ; clayTerminalPromotionIsFalse = Final.nsFinalStateKeepsTerminalFalse
    ; statement = paperInterfaceStatement
    ; statementIsCanonical = refl
    }

nsPaperInterfaceClayFalse :
  Final.clayNavierStokesPromoted
    (finalStateReceipt canonicalNSPaperTheoremStatus)
  ≡ false
nsPaperInterfaceClayFalse = refl

nsPaperInterfaceTerminalFalse :
  clayTerminalPromotion canonicalNSPaperTheoremStatus ≡ false
nsPaperInterfaceTerminalFalse = Final.nsFinalStateKeepsTerminalFalse

nsPaperLiteralClayTargetImplemented :
  Clay23.literalFeffermanPeriodicStatementImplemented
    (clayContractRound23 canonicalNSPaperTheoremStatus)
  ≡ true
nsPaperLiteralClayTargetImplemented = Clay23.literalTargetIsImplemented
