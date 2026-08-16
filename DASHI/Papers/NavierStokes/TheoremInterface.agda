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
-- ROUND62 MATHEMATICAL COMPRESSION + CONCRETE FALSIFICATION
--
-- A: the HH-bad affine alpha/beta recurrence is removed from the required
-- producer path.  Normalizing the literal successor identity gives exactly
--
--   C_(q+1) = I_(q+1) + N_q,
--
-- so finite prefix plus N_q<=C_*-I_(q+1) closes the ceiling directly.  The
-- literal density comparison 2^q g_q<=C_q feeds the selected normalized
-- profile, and the physical unmasked-charge estimate Q_q<=K_bad D gives the
-- exact hard tax eta_HHb=2 C_* K_bad.  The lower trajectory audit confirms the
-- remaining A1 object is the actual differentiated projected shell identity;
-- it is not hidden in the finite seven-term algebra.
--
-- B: the Round58 Q-valued normalized Gram object is only a rational
-- certificate.  Round62 now constructs literal same-carrier cross-pairing and
-- fibre-mass diagnostics and evaluates one canonical active odd-P/Q transport
-- entry exactly: p=(1,0,0), q=(1,1,0), k=(2,1,0), cutoff=0 gives coefficient
-- -i, hence a nonzero active entry on every compatible nontrivial field.
--
-- That concrete calculation also rejects the wrong self-mass normalization:
-- a unit same-fibre correlation normalized by its own two masses gives 1, but
-- the required same-shell coefficient is <=17/64<1.  Therefore the cross-Gram
-- object is diagnostic only.  The correct physical B target is the existing
-- Round49/53 Schur squared-output coefficient
--
--   ||oddPQ input||^2 <= rowMass * X.
--
-- Round54 already supplies the output-fibre Schur reducer, Round55 aggregates
-- same/adjacent values to 133/256, and Round35/40 reduce the two adjoint faces
-- to one normalized Gram factorization.  The remaining B theorem is precisely
-- that same-object factorization/common-hat realization plus the active
-- 17/64,65/512,65/512 overlap/row bounds.
--
-- C: aggregate data headroom is no longer an opaque nine-owner field.  Six
-- owner data remainders are zero.  On the preferred exact-independent-kernel-
-- zero branch kernel vanishes entirely and
--
--   a = a_smooth-HHg + a_Com.
--
-- The singular/parabolic HH-good part is data-free.  The remaining global C
-- estimate is X_n<=K C r^n on the same owner->flux->block object.  Round62 adds
-- one-block counterexamples that immediately refute bad candidate K, HH-good,
-- Com or combined two-soft scales, and a dependency no-go forbids deriving K
-- from the final correction headroom whose B_* already depends on K.  If K>0
-- and a<r-q, Round61 constructs the maximal B_*=((r-q)-a)/K.
--
-- D/F: one structured localized-PDE atom list produces the interior, kernel
-- and lower/upper boundary ledgers.  Exact cancellation pairs are folded
-- structurally.  The later finite complex increment-kernel module already
-- proves the spatial-increment/four-transform equality, finite-fold transport,
-- and rp1/rp2/hard-tail three-piece identity.  Thus the missing D1 theorem is
-- narrower: identify the OFFICIAL opaque full-shell Pair enumerator with that
-- finite literal two-mode pair system on the selected solution and emit the
-- structured atoms.  Exact independent-kernel zero would then delete kernel
-- production, eta, data and critical cost; otherwise a quantitative fallback
-- remains necessary.  Physical boundary limits remain F2.
--
-- E: fourth-order shell decay M*2^(-j) already implies finite L1 partial mass
-- <=2M.  Round62 now proves that lattice restriction alone cannot determine a
-- continuum multiplier: two explicit continuum extensions agree on every
-- embedded ProjectionMode yet differ off-lattice.  Therefore E1 must actually
-- construct/select the C_c^4 annular continuum cutoff/matrix multiplier whose
-- restriction is Round48; only then can E2 perform four integrations by parts.
-- The old NS bump sprints close this only by external Rudin/Grafakos authority,
-- and the Bishop power-series lane still lacks the needed unconditional
-- elementary-function derivative calculus, so neither is silently promoted.
--
-- G: after substituting the maximal B_* and deleting kernel on the preferred
-- branch, S=s_Com+s_HHg and
--
--   2 C_* K_bad + K S^2 / ((r-q)-a) + 1/16 < 1.
--
-- Round62 solves its exact necessary feasibility region:
--
--   C_* K_bad < 15/32,
--   K S^2 < (15/16 - 2 C_* K_bad) ((r-q)-a).
--
-- H remains closed on the same selected Leray--Hopf/Luo continuation carrier.
--
-- Consequently the remaining Clay frontier is genuinely physical/analytic:
-- selected-trajectory A; one normalized literal Com Gram/Schur realization;
-- upstream C scales; the official-Pair-to-finite-literal D/F bridge plus
-- zero/limits; an actually constructed C_c^4 continuum annular multiplier and
-- its fourfold Fourier decay; and the final instantiated scalar gate.
------------------------------------------------------------------------

paperInterfaceStatement : String
paperInterfaceStatement =
  "Paper-facing NS interface: Round62 removes the HH-bad affine recurrence; proves a concrete canonical active odd-PQ transport entry is exactly -i and nonzero; rejects self-mass cross-Gram normalization because it self-normalizes to 1 while the physical same-shell Schur row coefficient must be <=17/64; identifies Round49/54 Schur row mass as the correct B target; adds one-block C falsifiers and forbids circular derivation of K from B_*; recognizes that the finite complex increment-kernel coefficient/fold algebra is already closed and narrows D1 to the official opaque-Pair realization; proves lattice restriction does not determine a continuum multiplier, so E1 must construct the actual C_c^4 annular extension before fourfold IBP; retains the kernel-zero two-soft gate 2 C_* K_bad + K S^2/((r-q)-a) + 1/16 < 1 and its necessary feasibility region. Genuine selected-solution A/B/C/D/F/E producers and the instantiated scalar gate remain open; Clay Navier-Stokes and terminal promotion remain false."

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
