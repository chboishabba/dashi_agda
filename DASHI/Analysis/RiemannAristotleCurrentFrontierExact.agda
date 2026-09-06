module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- Maintained bidirectionally: forward from machine-checked Lean owners and
-- backward from the unweakened RH contradiction.
--
-- NEWEST CHECKED LEAN ADVANCE (2026-09-06)
--
-- The reproduced Zeta23Bridge tranche reports 8894 jobs before the two new
-- modules and 8896 jobs after them. Section 37 reconciles the density cutoff
-- with the quarter-period requirement; Section 38 instantiates the upper-count
-- hypotheses for the repository's actual zeta zeros using the checked
-- Zeta23.RvM.zetaZeroConfig_local_count theorem.
--
-- Section 37 proves that, at D = pi/(3 Lambda), the density cutoff is
--
--   (pi/3 + pi^3 A/(6c))/Lambda + (1 + pi^2 A/(2c)),
--
-- and that the leading compatibility window is nonempty exactly when
-- c < pi^2 A (for c > 0). It also gives an actual Nat cutoff in the joint
-- window under the stated hypotheses. Therefore the density cut does NOT
-- refute the adaptive inverse-width route; it converts it into a constant-
-- window compatibility problem on J*Lambda.
--
-- Section 38 supplies the zeta unit-window upper count and derives the needed
-- short-window upper count by finite unit-window covering. Hence the upper
-- counting hypothesis is no longer open for zeta. The checked imported Lean
-- theorem is proof-carrying mathematics: it is neither an unproved authority
-- receipt nor an Agda proof.
--
-- CURRENT NEAR-CORE FRONTIER
--
-- The first live analytic obligation is the genuine clustering statement
--
--   (4/pi^2) * highGapMass < lowGapMass,
--
-- for the actual zeta zeros at D = pi/(3 Lambda).
--
-- The current highest-alpha refinement is a SAME-target/SAME-window second
-- moment of the target-relative ORDINATE gap
--
--   delta = Im(rho) - t.
--
-- This is deliberately NOT the Alpöge--Furman/Hermitian transverse coordinate
-- alpha = Re(rho)-1/2. A proof-bearing finite collision now records that equal
-- alpha information can coexist with different delta information, so the
-- transverse moment cannot directly close local gap clustering.
--
-- The correct in-repo carrier is PoleNearPhaseStatistic.targetRelativeGap. The
-- moment socket is indexed by the already-existing ActualSelectedPoleNearProducer,
-- reusing its selected target, multiplicities and nearOffFinset rather than
-- creating a parallel zero/window object.
--
-- Agda owns the subtraction-free compiler
--
--   highGapMass <= M2_delta_norm < 2*lowGapMass
--     -> highGapMass < 2*lowGapMass.
--
-- Together with the elementary real coefficient fact 4/pi^2 < 1/2 this is
-- sufficient for the exact clustering coefficient. The actual selected-window
-- delta-moment producer remains open. The same delta coordinate also occurs in
-- the literal finite-near cosine phase cos((b_sigma-t)u), so a successful
-- target-gap statistic may feed both clustering and finite-near evaluation.
--
-- Earlier finite-near Schur and nuisance-elimination obligations remain valid
-- architectural dependencies. Gamma precision, low-ordinate/global coverage,
-- and the final RH implication remain open where recorded.
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

    quarterPeriodDensityReconciliationClosedInLean : Bool
    quarterPeriodDensityReconciliationClosedInLeanIsTrue :
      quarterPeriodDensityReconciliationClosedInLean ≡ true

    zetaUnitLocalCountClosedInLean : Bool
    zetaUnitLocalCountClosedInLeanIsTrue :
      zetaUnitLocalCountClosedInLean ≡ true

    zetaShortWindowUpperCountClosedInLean : Bool
    zetaShortWindowUpperCountClosedInLeanIsTrue :
      zetaShortWindowUpperCountClosedInLean ≡ true

    densityCutRefutesInverseWidthRoute : Bool
    densityCutRefutesInverseWidthRouteIsFalse :
      densityCutRefutesInverseWidthRoute ≡ false

    zetaLongWindowLowerDensityClosed : Bool
    zetaLongWindowLowerDensityClosedIsFalse :
      zetaLongWindowLowerDensityClosed ≡ false

    actualZetaClusteringClosed : Bool
    actualZetaClusteringClosedIsFalse : actualZetaClusteringClosed ≡ false

    targetLocalSecondMomentCompilerClosedInAgda : Bool
    targetLocalSecondMomentCompilerClosedInAgdaIsTrue :
      targetLocalSecondMomentCompilerClosedInAgda ≡ true

    targetLocalSecondMomentProducerClosed : Bool
    targetLocalSecondMomentProducerClosedIsFalse :
      targetLocalSecondMomentProducerClosed ≡ false

    targetLocalMomentUsesExistingSelectedWindow : Bool
    targetLocalMomentUsesExistingSelectedWindowIsTrue :
      targetLocalMomentUsesExistingSelectedWindow ≡ true

    transverseMomentDirectlyControlsOrdinateClustering : Bool
    transverseMomentDirectlyControlsOrdinateClusteringIsFalse :
      transverseMomentDirectlyControlsOrdinateClustering ≡ false

    alpogeFurmanGlobalSimpleProportionDirectlyClosesClustering : Bool
    alpogeFurmanGlobalSimpleProportionDirectlyClosesClusteringIsFalse :
      alpogeFurmanGlobalSimpleProportionDirectlyClosesClustering ≡ false

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
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The newest checked Lean tranche reconciles the quarter-period lower cutoff with the density upper cutoff and discharges the zeta unit/short-window upper-count hypotheses. The first live optimized near-core obligation is genuine zeta clustering at D = pi/(3 Lambda). Its current highest-alpha refinement is a SAME-selected-window second moment of delta = Im(rho)-t, not the unrelated transverse alpha = Re(rho)-1/2 coordinate. Agda owns the moment-to-two-to-one ratio compiler and the same-object selected-window attachment shape; the actual analytic delta-moment producer and elementary 4/pi^2 < 1/2 coefficient bridge remain open. The same delta coordinate is also the phase variable in the finite-near cosine sum, so this producer may feed both zero-side consumers. Earlier finite-near, Gamma, low-ordinate and final RH obligations remain open where recorded; RH is not derived."
