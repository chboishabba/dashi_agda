module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- Maintained bidirectionally: forward from exact source owners and backward
-- from the unweakened RH contradiction.
--
-- CLOSED IN LEAN / EXISTING BRIDGE
--
--  * universal positive same-ordinate observer construction;
--  * two-radius cluster height defect: positive for an off-line fibre and zero
--    for an entirely critical-line fibre;
--  * high-ordinate prime projective defect exactly zero;
--  * deterministic Gamma/pole projective response vectors and generic exact
--    two-nuisance Schur algebra;
--  * target defect has exact r^2 leading coefficient plus r^4 remainder;
--  * functional-equation reflection pairing cancels the odd-height channel;
--  * reflection-symmetrized far-zero carrier has a uniform curvature envelope;
--  * unit ordinate shells plus unconditional local zero counts prove absolute
--    summability of the m_rho/(Im rho-t)^2 carrier and hence absolute
--    convergence of the reflection far tail for every compactly supported C2
--    real-even taper.
--
-- NEW BIDI CORRECTION FROM THE 2026-08-30 LEAN SESSION
--
-- The proposed socket
--
--   ||E D_off||^2 <= B_far <
--     det3(D_pole,D_Gamma,D_cluster)^2 / wedgeSq(D_pole,D_Gamma)
--
-- cannot be the final strict-budget theorem when the deterministic Schur
-- identity gives
--
--   E D_cluster = E D_off.
--
-- The right-hand margin is precisely ||E D_cluster||^2, hence the same real
-- quantity as ||E D_off||^2.  No upper bound on the whole post-Schur carrier can
-- be strictly below that same quantity.
--
-- Therefore the literal zero carrier must be split first:
--
--   D_off = D_targetCluster + D_remainder,
--
-- in the SAME post-Schur coordinates.  The strict estimate applies only to the
-- genuine remainder.  Absolute convergence now guarantees that this remainder
-- is mathematically well-defined; it does not by itself provide cancellation.
--
-- HIGHEST-ALPHA LIVE CUTSET
--
--   T1. literal post-Schur target/remainder identity on the actual zero carrier;
--
--   T2. construct/retain a quantitative target lower margin for the target
--       same-ordinate cluster in those exact coordinates;
--
--   T3. prove a signed cancellation estimate for the genuine reflection-
--       symmetrized remainder, strictly below that target margin.  The new Lean
--       curvature/shell work closes convergence and supplies the summable
--       delta^-2 envelope, but not this strict inequality;
--
--   T4. close the deterministic short three-taper rank/survival construction if
--       it is still used to eliminate Gamma/pole exactly;
--
--   T5. certify the complementary low-ordinate region, or replace the split by
--       a universal construction;
--
--   T6. invoke the already-owned target/remainder margin contradiction and the
--       repository's existing unweakened RH proposition.
--
-- No theorem here derives RH.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AristotleCurrentFrontier : Set where
  constructor aristotle-current-frontier
  field
    universalEvenConeConstructionClosedInLean : Bool
    universalEvenConeConstructionClosedInLeanIsTrue :
      universalEvenConeConstructionClosedInLean ≡ true

    twoRadiusOffLineDiscriminatorClosedInLean : Bool
    twoRadiusOffLineDiscriminatorClosedInLeanIsTrue :
      twoRadiusOffLineDiscriminatorClosedInLean ≡ true

    highOrdinatePrimeProjectiveDebtZeroInLean : Bool
    highOrdinatePrimeProjectiveDebtZeroInLeanIsTrue :
      highOrdinatePrimeProjectiveDebtZeroInLean ≡ true

    targetLeadingCoefficientAndRemainderClosedInLean : Bool
    targetLeadingCoefficientAndRemainderClosedInLeanIsTrue :
      targetLeadingCoefficientAndRemainderClosedInLean ≡ true

    reflectionPairKernelClosedInLean : Bool
    reflectionPairKernelClosedInLeanIsTrue : reflectionPairKernelClosedInLean ≡ true
    reflectionFarTailAbsoluteConvergenceClosedInLean : Bool
    reflectionFarTailAbsoluteConvergenceClosedInLeanIsTrue :
      reflectionFarTailAbsoluteConvergenceClosedInLean ≡ true
    uniformReflectionCarrierCurvatureClosedInLean : Bool
    uniformReflectionCarrierCurvatureClosedInLeanIsTrue :
      uniformReflectionCarrierCurvatureClosedInLean ≡ true
    latestLeanBridgeBuildKernelChecked : Bool
    latestLeanBridgeBuildKernelCheckedIsTrue :
      latestLeanBridgeBuildKernelChecked ≡ true

    wholePostSchurCarrierStrictBudgetValid : Bool
    wholePostSchurCarrierStrictBudgetValidIsFalse :
      wholePostSchurCarrierStrictBudgetValid ≡ false

    literalTargetRemainderSplitClosed : Bool
    literalTargetRemainderSplitClosedIsFalse :
      literalTargetRemainderSplitClosed ≡ false
    strictSignedRemainderCancellationClosed : Bool
    strictSignedRemainderCancellationClosedIsFalse :
      strictSignedRemainderCancellationClosed ≡ false
    deterministicNuisanceThreeTaperConstructionClosed : Bool
    deterministicNuisanceThreeTaperConstructionClosedIsFalse :
      deterministicNuisanceThreeTaperConstructionClosed ≡ false
    lowOrdinateComplementCertified : Bool
    lowOrdinateComplementCertifiedIsFalse :
      lowOrdinateComplementCertified ≡ false

    finalRHImplicationClosed : Bool
    finalRHImplicationClosedIsFalse : finalRHImplicationClosed ≡ false
    boundedReading : String

open AristotleCurrentFrontier public

canonicalAristotleCurrentFrontier : AristotleCurrentFrontier
canonicalAristotleCurrentFrontier =
  aristotle-current-frontier
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The newest kernel-checked Lean tranche closes uniform reflection-pair curvature control and absolute summability/convergence of the literal far zero carrier. Bidirectional checking also kills the old whole-carrier B_far socket: after deterministic Schur, D_cluster and D_off have the same residual vector, so that whole carrier cannot be budgeted strictly below its own Schur margin. The live target is now a literal target-cluster plus genuine-remainder decomposition, followed by a signed cancellation estimate on the convergent remainder only, together with the deterministic three-taper construction and low-ordinate certification before the existing final RH compiler can fire."
