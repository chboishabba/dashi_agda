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
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound61Exact
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
-- Round55 imports the six A--F cutset modules. Round59/60 sharpened the
-- quantitative A--C boundaries. Round61 then removes several artificial
-- producer obligations rather than adding another receipt layer:
--
-- * A3: 2^q g_q need only be dominated by the selected recurrence defect;
--   unmasked charge may carry a physical K_bad factor, giving exactly
--   eta_HHb=(2 C_*) K_bad rather than assuming K_bad=1.
-- * B2/B3: one active same-object equality from the literal normalized odd-PQ
--   pair product to the existing six-three Gram cell derives 17/64,
--   65/512, 65/512 and the whole-fibre 133/256 endpoint. B3 is not an
--   independent physical premise.
-- * C2/C3: a positive fixed-shift correction forces a<r-q. Conversely C1
--   scale bounds plus a<r-q construct a positive correction automatically:
--   the zero-safe branch uses ((r-q)-a)/(K+1), while for K>0 the sharp branch
--   uses the maximal B_*=((r-q)-a)/K and saturates a+B_*K=r-q exactly.
-- * ABC: the compiler-light canonical source is now constructed from A's
--   source-indexed estimates, B's single active six-three same-object theorem,
--   and C's strict-positive scale data; callers do not resupply derived B/C
--   certificates.
-- * C->G: the final resource carrier receives the sharp positive-K B_* from C
--   definitionally rather than accepting another arbitrary correction cap.
-- * G: equal B_*/3 allocation remains an exact fallback. The high-alpha path
--   uses rational square-root majorants c_i<=s_i^2, allocates B_i proportional
--   to s_i, and obtains exact soft tax S^2/B_* with
--   S=s_Com+s_kernel+s_HHg. This approaches the Cauchy-optimal real allocation
--   without irrational carriers. The final strict scalar gate is consumed
--   directly, and the necessary two-resource no-go carries K_bad.
-- * H: continuation is audited on the already-existing official selected
--   Leray--Hopf/Luo carrier, not on a separate receipt carrier.
--
-- The genuine remaining producer frontier is therefore A1/A2, B1, C1/C2,
-- D1/F1 plus their residual/limit estimates, and E2.  The terminal Clay bit
-- remains false until those literal PDE/Fourier producers are actually proved.
------------------------------------------------------------------------

paperInterfaceStatement : String
paperInterfaceStatement =
  "Paper-facing NS interface: Round61 compresses the physical Clay cutset without promoting the theorem. A3 uses normalized-density domination and explicit K_bad charge multiplicity; B3 follows from one active literal-normalized-PQ to six-three-Gram same-object theorem; C3 is constructed from C1 plus a<r-q, sharply as ((r-q)-a)/K for K>0; the canonical ABC root constructs derived B/C certificates; C feeds its sharp B_* directly into G; G has an exact equal-third fallback and a sharper rational square-root-majorant allocation with soft tax S^2/B_*, plus a K_bad-aware two-resource no-go; H is closed on the official selected Leray-Hopf/Luo carrier. Genuine physical A1/A2, B1, C1/C2, D/F and E2 producers remain open, so Clay Navier-Stokes and terminal promotion remain false."

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