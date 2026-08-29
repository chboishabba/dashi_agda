module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- Maintained bidirectionally: forward from machine-checked Lean owners and
-- backward from the unweakened RH contradiction.
--
-- NEWEST KERNEL-CHECKED LEAN ADVANCE (2026-08-30)
--
-- The supplied Zeta23Bridge session reports `lake build Zeta23Bridge`
-- successful (8883 jobs) and the capstone axiom audit returning only
-- propext/Classical.choice/Quot.sound.
--
-- It now owns, for every cutoff J >= 1,
--
--   farShellBound A |t| J
--     = 18 A log(|t|+4)/J + 72 A/sqrt(J),
--
-- together with:
--
--   * a proof that the literal zero tail is bounded by that expression;
--   * convergence of this explicit bound to zero and arbitrary-accuracy cutoff
--     selection;
--   * a genuinely finite signed near shell carrier;
--   * transport of the decomposition onto the literal offOrdProjectiveDefect:
--
--       |D_off(g,t,r) - 1/2 nearSignedSum(t,J)|
--         <= 1/2 C farShellBound A |t| J.
--
-- The aggregate root also imports LiteralWeilDeterministicProjectiveSchur, so
-- the previously source-only deterministic Schur compiler is now part of this
-- reported kernel-checked Lean build.
--
-- BIDI CONSEQUENCE
--
-- The infinite part of S2 is no longer a research socket.  For a three-taper
-- observer, let E denote exact elimination of the deterministic pole/Gamma
-- response vectors and let D_near(J) be the three-vector of finite signed near
-- sums.  Write
--
--   X = E D_off,
--   N = E D_near(J),
--   F = E (D_off - D_near(J)).
--
-- Then X = N + F, and the remaining finite theorem may be targeted through
--
--   ||X||^2 <= 2 ||N||^2 + 2 ||F||^2.
--
-- The far term F is mechanically controlled by the explicit cutoff theorem plus
-- Schur contraction.  Therefore the genuinely open S2 object is the finite
-- signed post-Schur near-core energy ||N||^2, not the infinite zero tail.
--
-- CURRENT RESEARCH CUTSET
--
--   S1. construct a short three-taper family such that the deterministic
--       pole/Gamma vectors have rank two and the off-line same-ordinate cluster
--       survives with an explicit positive Schur margin M_cluster;
--
--   S2a. CLOSED IN LEAN: explicit far-shell cutoff formula and literal D_off
--        finite-near/far decomposition;
--
--   S2b. prove a signed bound on the FINITE post-Schur near vector
--
--          ||E D_near(J)||^2 <= B_near(J)
--
--        for a jointly chosen cutoff J;
--
--   S2c. combine that finite bound with the explicit Lean far remainder so that
--
--          2 B_near(J) + 2 B_error(J) < M_cluster.
--
--        `RiemannAristotleFiniteNearCoreSchurCompilerExact` then closes the
--        strict off-carrier contradiction mechanically;
--
--   S3. certify the complementary low-ordinate region, or replace the split by
--       a universal construction;
--
--   S4. invoke the repository's existing unweakened RH proposition.
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

    deterministicProjectiveSchurKernelCheckedInLean : Bool
    deterministicProjectiveSchurKernelCheckedInLeanIsTrue :
      deterministicProjectiveSchurKernelCheckedInLean ≡ true

    explicitFarShellCutoffBoundClosedInLean : Bool
    explicitFarShellCutoffBoundClosedInLeanIsTrue :
      explicitFarShellCutoffBoundClosedInLean ≡ true

    explicitFarShellTendsToZeroClosedInLean : Bool
    explicitFarShellTendsToZeroClosedInLeanIsTrue :
      explicitFarShellTendsToZeroClosedInLean ≡ true

    finiteSignedNearCarrierClosedInLean : Bool
    finiteSignedNearCarrierClosedInLeanIsTrue :
      finiteSignedNearCarrierClosedInLean ≡ true

    literalDoffCutoffCarrierClosedInLean : Bool
    literalDoffCutoffCarrierClosedInLeanIsTrue :
      literalDoffCutoffCarrierClosedInLean ≡ true

    latestLeanBridgeBuildKernelChecked : Bool
    latestLeanBridgeBuildKernelCheckedIsTrue :
      latestLeanBridgeBuildKernelChecked ≡ true

    nearFarShellCompositionCompilerClosedInAgda : Bool
    nearFarShellCompositionCompilerClosedInAgdaIsTrue :
      nearFarShellCompositionCompilerClosedInAgda ≡ true

    nearFarAllowanceCompilerClosedInAgda : Bool
    nearFarAllowanceCompilerClosedInAgdaIsTrue :
      nearFarAllowanceCompilerClosedInAgda ≡ true

    finiteNearCoreSchurPerturbationCompilerClosedInAgda : Bool
    finiteNearCoreSchurPerturbationCompilerClosedInAgdaIsTrue :
      finiteNearCoreSchurPerturbationCompilerClosedInAgda ≡ true

    explicitLeanTailFormulaTransportedAsAgdaProof : Bool
    explicitLeanTailFormulaTransportedAsAgdaProofIsFalse :
      explicitLeanTailFormulaTransportedAsAgdaProof ≡ false

    finiteSignedNearSchurCancellationClosed : Bool
    finiteSignedNearSchurCancellationClosedIsFalse :
      finiteSignedNearSchurCancellationClosed ≡ false

    jointFiniteNearFarMarginClosed : Bool
    jointFiniteNearFarMarginClosedIsFalse :
      jointFiniteNearFarMarginClosed ≡ false

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
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The newest kernel-checked Lean tranche closes the explicit far-shell modulus, arbitrary-accuracy cutoff selection, the finite signed near carrier, and the literal D_off finite-near/far decomposition. The deterministic projective Schur compiler is also now inside the reported aggregate build. Agda therefore moves the first unproved S2 theorem to the finite post-Schur near-core energy: bound ||E D_near(J)||^2 strongly enough that its weighted sum with the explicit far-error energy lies below the surviving S1 cluster margin. The infinite zero tail is no longer the research bottleneck. S1 and low-ordinate certification remain open; RH is not derived."
