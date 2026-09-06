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
-- The live clustering statement is
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
-- This is deliberately NOT the Alpoge--Furman/Hermitian transverse coordinate
-- alpha = Re(rho)-1/2. Equal alpha information can coexist with different delta
-- information, so transverse-moment control is not a direct clustering donor.
--
-- BIDI compression has now removed another duplicate interface. The existing
-- DirectFinitePoleNearProducer already carries ZeroIndex, nearIndex,
-- multiplicity, targetRelativeGap and a signed approximant/error receipt.
-- Therefore PoleNearPhaseStatistic is compiler output from that direct producer;
-- a second phase-statistic carrier is not a research theorem.
--
-- The remaining SAME-OBJECT representation payment is narrower: identify that
-- direct producer with the existing ActualSelectedPoleNearProducer. This
-- SelectedDirectFiniteWeld is shared upstream of both the delta-moment clustering
-- route and the finite-near signed evaluation. It prevents those two consumers
-- from silently using different zero families, targets, cutoffs or multiplicity
-- functions.
--
-- Agda owns the subtraction-free compiler
--
--   highGapMass <= M2_delta_norm < 2*lowGapMass
--     -> highGapMass < 2*lowGapMass.
--
-- Together with the elementary real coefficient fact 4/pi^2 < 1/2 this is
-- sufficient for the exact clustering coefficient. The actual welded-window
-- delta-moment estimate remains open. The direct producer's numerical finite-
-- near evaluation also remains open at consumer-sufficient precision.
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

    concretePhaseStatisticCompilerClosedInAgda : Bool
    concretePhaseStatisticCompilerClosedInAgdaIsTrue :
      concretePhaseStatisticCompilerClosedInAgda ≡ true

    selectedDirectZeroCarrierWeldClosed : Bool
    selectedDirectZeroCarrierWeldClosedIsFalse :
      selectedDirectZeroCarrierWeldClosed ≡ false

    oneDirectGapCarrierFeedsClusteringAndFiniteNear : Bool
    oneDirectGapCarrierFeedsClusteringAndFiniteNearIsTrue :
      oneDirectGapCarrierFeedsClusteringAndFiniteNear ≡ true

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
    "The checked Lean tranche reconciles quarter-period versus density cutoffs and closes the zeta unit/short-window upper-count input. The live optimized near-core target is actual-zeta low-gap clustering at D = pi/(3 Lambda). Its highest-fanout refinement uses delta = Im(rho)-t on one SAME selected/direct zero carrier. PoleNearPhaseStatistic is now compiler output from DirectFinitePoleNearProducer, so a second phase carrier is pruned. The remaining representation seam is the SelectedDirectFiniteWeld identifying that direct producer with the existing ActualSelectedPoleNearProducer. Once welded, the same targetRelativeGap/multiplicity/nearIndex carrier can feed both the normalized delta^2 moment and the signed finite-near evaluation. Agda owns the moment-to-two-to-one ratio compiler; the actual delta-moment estimate, exact 4/pi^2 coefficient transport, consumer-sufficient finite-near evaluation, Gamma precision, low-ordinate coverage and final RH implication remain open. Transverse alpha moments and global >2/3 simple-zero abundance are not silently promoted to local ordinate clustering. RH is not derived."
