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
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound62Exact
import DASHI.Papers.NavierStokes.ClayContractRound23 as Clay23

------------------------------------------------------------------------
-- Paper-facing Navier-Stokes theorem/status interface.
--
-- This module remains a non-promoting paper spine.  The literal periodic Clay
-- target is represented, but the terminal theorem remains false until the
-- genuine physical producer lemmas are proved.
--
-- ROUND62 MATHEMATICAL COMPRESSION
--
-- A: the HH-bad affine alpha/beta recurrence is removed from the required
-- producer path.  Normalizing the literal successor identity gives exactly
--
--   C_(q+1) = I_(q+1) + N_q,
--
-- so finite prefix plus N_q<=C_*-I_(q+1) closes the ceiling directly.  The
-- literal density comparison 2^q g_q<=C_q feeds the selected normalized
-- profile, and the physical unmasked-charge estimate Q_q<=K_bad D gives the
-- exact hard tax eta_HHb=2 C_* K_bad.
--
-- B: Round58's Q-valued normalized Gram object is now explicitly only a
-- rational certificate carrier.  The same-object physical endpoint keeps the
-- normalized energy in `Carrier (realField model)`, the exact algebraic real
-- field already selected by the literal `PeriodicHardShellFourierPDE`.  An
-- `OrderedRealExtension` plus a rational embedding of THAT carrier is enough to
-- turn active bounds by embedded 17/64 and 65/512 into the embedded 133/256
-- bandwidth-one bound.  Murray--Bishop reals remain a concrete setoid backend,
-- but are not definitionally identified with this propositional-equality
-- Fourier carrier.  The remaining B theorem is to construct the normalized
-- operator-product energy in the literal carrier and prove common-hat plus the
-- same/adjacent active bounds.
--
-- C: aggregate data headroom is no longer an opaque nine-owner field.  Six
-- owner data remainders are already zero.  The fallback coefficient is
-- a_HHg+a_Com+a_kernel.  On the preferred exact-independent-kernel-zero branch,
-- kernel vanishes as an owner entirely and the strict-gap coefficient is
--
--   a = a_HHg + a_Com.
--
-- Moreover the singular/parabolic HH-good owner has data remainder zero, so
-- a_HHg is only the smooth periodic correction scale.  The remaining global C
-- estimate is X_n<=K C r^n on the same owner->flux->block object.  If K>0 and
-- a<r-q, Round61 already constructs the maximal
--
--   B_* = ((r-q)-a)/K.
--
-- D/F: one structured localized-PDE atom list now produces the interior,
-- kernel and lower/upper boundary ledgers.  Exact kernel cancellation pairs are
-- folded structurally.  If the literal independent total is zero, the existing
-- structural kernel-zero owner follows and has production=eta=data=critical=0.
-- Only the actual localized PDE extraction, independent-zero/estimate, and
-- classified boundary limits remain analytic.
--
-- E: once four inverse-Fourier integrations by parts produce shell mass
-- M*2^(-j) in dimension three, exact geometric algebra proves every finite L1
-- partial mass <=2M.  Thus the remaining E theorem is the same-object continuum
-- annular multiplier plus that literal fourfold integration-by-parts estimate;
-- no separate Schwartz-to-L1 authority is needed.
--
-- G: after substituting the maximal B_* and deleting kernel on the preferred
-- branch, S=s_Com+s_HHg and the final gate is
--
--   2 C_* K_bad + K S^2 / ((r-q)-a) + 1/16 < 1.
--
-- Round62 solves its exact feasibility region:
--
--   C_* K_bad < 15/32,
--   K S^2 < (15/16 - 2 C_* K_bad) ((r-q)-a).
--
-- H remains closed on the same selected Leray--Hopf/Luo continuation carrier.
--
-- Consequently the remaining Clay frontier is genuinely physical/analytic:
-- selected-solution Duhamel/headroom+density+charge; literal-field normalized
-- Com construction/bounds; same-object C scale estimates; one localized PDE
-- atom extraction plus kernel/boundary limits; continuum annular fourfold
-- Fourier decay; and the final instantiated scalar gate.  None is promoted
-- here by a receipt.
------------------------------------------------------------------------

paperInterfaceStatement : String
paperInterfaceStatement =
  "Paper-facing NS interface: Round62 removes the HH-bad affine recurrence from the producer cutset; keeps physical normalized Com energy in the literal Fourier model's own ordered real field, with rational constants only as embedded majorants and Bishop reals only as a separate setoid backend; reduces the preferred fixed-shift data coefficient to smooth-HH-good plus Com when the independent kernel is exactly zero; derives kernel and boundary ledgers from one structured localized-PDE atom source; closes fourth-order dyadic decay to uniform L1 summability; substitutes the sharp B_*=((r-q)-a)/K into the weighted allocator; and solves the preferred feasibility region C_* K_bad<15/32 and K S^2<(15/16-2 C_* K_bad)((r-q)-a). Genuine selected-solution A/B/C/D/F/E physical producers and the instantiated scalar gate remain open; Clay Navier-Stokes and terminal promotion remain false."

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
