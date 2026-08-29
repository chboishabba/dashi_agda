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
--    real-even taper;
--  * the newest supplied session reports `lake build Zeta23Bridge` successful
--    and the extended axiom audit returning only the standard Mathlib axioms.
--
-- SOURCE-AUDITED BIDI READING OF THE STRICT MARGIN SOCKET
--
-- `D_off` is defined on the complement of `SameOrd t`; it does NOT contain the
-- target same-ordinate cluster.  After short-support prime annihilation and
-- exact deterministic Schur elimination, the literal explicit-formula balance
-- gives
--
--   E D_cluster = E D_off.
--
-- Therefore a genuine analytic theorem
--
--   ||E D_off||^2 <= B_far < ||E D_cluster||^2
--
-- is exactly the desired contradiction under an off-line target.  The no-go
-- says only that Schur/elimination algebra cannot manufacture that strict bound.
--
-- NEW AGDA S2 COMPILATION LAYER
--
-- Absolute convergence now permits an explicit shell cutoff J.  The infinite
-- cancellation theorem has been factored into
--
--   R_off <= R_near(J) + R_far(J)
--         <= B_near(J) + B_far(J)
--          < M_cluster.
--
-- `RiemannAristotleNearFarShellBudgetCompilerExact` proves this implication and
-- connects it directly to the whole-carrier contradiction.  The accompanying
-- producer sockets require:
--
--   * a quantitative curvature-times-tail envelope for the truly far shells;
--   * a FINITE SIGNED near-shell aggregate bound;
--   * one shared cutoff J;
--   * the strict combined budget margin.
--
-- The compiler does not prove either analytic producer.  In particular the
-- finite near core is not allowed to regress to the exhausted absolute W(t)
-- majorant.
--
-- HIGHEST-ALPHA LIVE CUTSET
--
--   S1. construct the short three-taper family so deterministic pole/Gamma
--       vectors have rank two and the off-line cluster survives the quotient
--       with an explicit positive Schur margin;
--
--   S2a. choose an explicit shell cutoff J and instantiate the kernel-checked
--        curvature/delta^-2 machinery as a quantitative B_far(J);
--
--   S2b. bound the finitely many nearby shells as one signed oscillatory core,
--        obtaining B_near(J), and prove
--
--          B_near(J) + B_far(J) < M_cluster;
--
--       the new Agda near/far compiler then yields the required strict whole-
--       carrier inequality mechanically;
--
--   S3. certify the complementary low-ordinate region, or replace the split by
--       a universal construction;
--
--   S4. invoke the already-owned whole-carrier cancellation contradiction and
--       the repository's existing unweakened RH proposition.
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

    wholePostSchurCarrierStrictBudgetIsContradictionTarget : Bool
    wholePostSchurCarrierStrictBudgetIsContradictionTargetIsTrue :
      wholePostSchurCarrierStrictBudgetIsContradictionTarget ≡ true
    eliminationAlgebraAloneClosesStrictBudget : Bool
    eliminationAlgebraAloneClosesStrictBudgetIsFalse :
      eliminationAlgebraAloneClosesStrictBudget ≡ false

    nearFarShellCompositionCompilerClosedInAgda : Bool
    nearFarShellCompositionCompilerClosedInAgdaIsTrue :
      nearFarShellCompositionCompilerClosedInAgda ≡ true
    quantitativeFarShellEnvelopeClosed : Bool
    quantitativeFarShellEnvelopeClosedIsFalse :
      quantitativeFarShellEnvelopeClosed ≡ false
    finiteSignedNearShellCoreClosed : Bool
    finiteSignedNearShellCoreClosedIsFalse :
      finiteSignedNearShellCoreClosed ≡ false
    combinedNearFarMarginClosed : Bool
    combinedNearFarMarginClosedIsFalse : combinedNearFarMarginClosed ≡ false

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
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The kernel-checked Lean tranche closes absolute convergence and uniform curvature control of the reflection-paired off-ordinate carrier. Agda now owns the exact cutoff compiler that turns a finite signed near-core budget plus a quantitative summable far-shell budget at one cutoff J into the strict whole-carrier bound and contradiction. The remaining S2 mathematics is therefore producer-side only: instantiate an explicit B_far(J), estimate the finite signed nearby shells as B_near(J), and beat the surviving S1 cluster margin. S1 deterministic three-taper construction and low-ordinate certification remain open; RH is not derived."
