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
-- The first live analytic obligation in this lane is the genuine clustering
-- statement
--
--   (4/pi^2) * highGapMass < lowGapMass,
--
-- for the actual zeta zeros at D = pi/(3 Lambda). The available coarse upper
-- counting theorem does not imply this.
--
-- The strongest in-repo refinement currently targets a SAME-target/SAME-window
-- normalized second moment. Agda now owns the subtraction-free compiler
--
--   highGapMass <= M2_norm < 2*lowGapMass
--     -> highGapMass < 2*lowGapMass,
--
-- while the actual analytic selected-window moment producer remains open. The
-- elementary real coefficient bridge 4/pi^2 < 1/2 then suffices to recover the
-- exact clustering coefficient. The Alpöge--Furman >2/3 simple/on-line theorem
-- is retained as a strong global donor but is explicitly non-descending to this
-- target-local consumer without an additional localization theorem.
--
-- Earlier finite-near Schur and nuisance-elimination obligations remain valid
-- architectural dependencies. Same-object finite-near evaluation, Gamma
-- precision, low-ordinate/global coverage, and the final RH implication remain
-- open where recorded.
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
    "The newest checked Lean tranche reconciles the quarter-period lower cutoff with the density upper cutoff and discharges the zeta unit/short-window upper-count hypotheses. The density cut therefore does not kill inverse-width scaling. The first live optimized near-core analytic obligation is genuine zeta clustering: (4/pi^2) * highGapMass < lowGapMass at D = pi/(3 Lambda). The current highest-alpha refinement is a SAME-target/SAME-window normalized second-moment producer: Agda already compiles highGapMass <= M2_norm < 2*lowGapMass into a strict highGapMass < 2*lowGapMass witness, while the actual analytic moment estimate and the elementary real coefficient bridge remain open. The Alpöge--Furman global >2/3 simple/on-line result does not directly descend to this local consumer. Earlier finite-near Schur, nuisance-elimination, low-ordinate, and final RH obligations remain open where recorded; RH is not derived."
