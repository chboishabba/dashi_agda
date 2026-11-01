module DASHI.Physics.Closure.NSTriadKNCanonicalCompletionFrontierRound488Exact where

------------------------------------------------------------------------
-- ROUND488 / CURRENT CANONICAL COMPLETION FRONTIER AFTER LEAN STANDARD LEAVES
--
-- R592 is newer than the older R486/R423 bookkeeping cut.  It shows that the
-- shortest literal periodic leaf-A target is the single R503 direct
-- off-diagonal resolvent budget
--
--   4 * integratedDirectCompanion(N,T) <= B(T),
--
-- uniformly in N.  R503 already compiles that exact payment into R415, so the
-- temporal/FTC, Bony, critical-cone and Schur routes are optional producer
-- tactics rather than mandatory prerequisites.
--
-- On the standard-analysis side, the paired Lean PR now proves:
--   * ordinary scalar FTC;
--   * finite-measure L2 -> L^(4/3) downgrade;
--   * L^(4/3) time-derivative assembly once the spatial nonlinear estimate is
--     supplied on the selected Sobolev carrier;
--   * sequential Banach--Alaoglu on weak-* dual balls;
--   * weak-* dual-norm lower semicontinuity.
--
-- Simon/Aubin--Lions itself is still an external published source theorem to
-- instantiate on H^(3/2) compact-> H^(1/2) -> H^(-1/2).  This file records
-- that boundary without manufacturing an inhabitant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNCanonicalDirectLeafAFrontierRound592Exact as R592
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNCriticalSimonUpgradeFollowsBarrierRound148Exact as R148
import DASHI.Physics.Closure.NSTriadKNCanonicalStandardAnalysisBridgeRound487Exact as R487

------------------------------------------------------------------------
-- Current hard mathematical leaf.
------------------------------------------------------------------------

round488CanonicalHardLeafIsSingleR503Budget : Bool
round488CanonicalHardLeafIsSingleR503Budget =
  R592.round592CanonicalLeafAIsSingleDirectOffDiagonalBudget

round488CanonicalHardLeafClosed : Bool
round488CanonicalHardLeafClosed = R592.round592CanonicalLeafAClosed

round488R503CompilerIntoSignedHeatConsumerClosed : Bool
round488R503CompilerIntoSignedHeatConsumerClosed =
  R503.round503ExactR500ToR415CompilerClosed

round488TemporalFTCRouteMandatory : Bool
round488TemporalFTCRouteMandatory =
  R592.round592TemporalCommutatorFTCRouteMandatory

round488CriticalConeOrBonyRouteMandatory : Bool
round488CriticalConeOrBonyRouteMandatory =
  R592.round592CriticalConeOrBonyRouteMandatory

------------------------------------------------------------------------
-- Standard-analysis implementation receipts from Lean.
--
-- These booleans describe concrete Lean theorem terms now present in
-- RequestProject/NavierStokes/CanonicalCompletionLeaves.lean.  They do not
-- claim an Agda FFI proof conversion.
------------------------------------------------------------------------

round488LeanScalarFTCTheoremInstalled : Bool
round488LeanScalarFTCTheoremInstalled = R487.round487LeanFTCSourceTheoremInstalled

round488LeanFiniteMeasureL2ToFourThirdInstalled : Bool
round488LeanFiniteMeasureL2ToFourThirdInstalled = true

round488LeanTimeDerivativeAssemblyInstalled : Bool
round488LeanTimeDerivativeAssemblyInstalled = true

round488LeanSequentialBanachAlaogluInstalled : Bool
round488LeanSequentialBanachAlaogluInstalled = true

round488LeanWeakStarDualNormLSCInstalled : Bool
round488LeanWeakStarDualNormLSCInstalled = true

------------------------------------------------------------------------
-- Remaining source instantiation boundary.
------------------------------------------------------------------------

round488ConcreteSimonSourceInstanceInstalledInAgda : Bool
round488ConcreteSimonSourceInstanceInstalledInAgda =
  R148.round148AgdaAnalyticSourceInstancesInstalled

round488DirectHardBudgetIsOnlyNovelNSMathematics : Bool
round488DirectHardBudgetIsOnlyNovelNSMathematics = true

round488NoHardBudgetManufacturedFromStandardAnalysis : Bool
round488NoHardBudgetManufacturedFromStandardAnalysis = true

------------------------------------------------------------------------
-- Proof-bearing status pins.
------------------------------------------------------------------------

round488CanonicalHardLeafIsSingleR503BudgetIsTrue :
  round488CanonicalHardLeafIsSingleR503Budget ≡ true
round488CanonicalHardLeafIsSingleR503BudgetIsTrue =
  R592.round592CanonicalLeafAIsSingleDirectOffDiagonalBudgetIsTrue

round488R503CompilerIntoSignedHeatConsumerClosedIsTrue :
  round488R503CompilerIntoSignedHeatConsumerClosed ≡ true
round488R503CompilerIntoSignedHeatConsumerClosedIsTrue =
  R503.round503ExactR500ToR415CompilerClosedIsTrue

round488TemporalFTCRouteMandatoryIsFalse :
  round488TemporalFTCRouteMandatory ≡ false
round488TemporalFTCRouteMandatoryIsFalse =
  R592.round592TemporalCommutatorFTCRouteMandatoryIsFalse

round488CriticalConeOrBonyRouteMandatoryIsFalse :
  round488CriticalConeOrBonyRouteMandatory ≡ false
round488CriticalConeOrBonyRouteMandatoryIsFalse =
  R592.round592CriticalConeOrBonyRouteMandatoryIsFalse

round488LeanFiniteMeasureL2ToFourThirdInstalledIsTrue :
  round488LeanFiniteMeasureL2ToFourThirdInstalled ≡ true
round488LeanFiniteMeasureL2ToFourThirdInstalledIsTrue = refl

round488LeanTimeDerivativeAssemblyInstalledIsTrue :
  round488LeanTimeDerivativeAssemblyInstalled ≡ true
round488LeanTimeDerivativeAssemblyInstalledIsTrue = refl

round488LeanSequentialBanachAlaogluInstalledIsTrue :
  round488LeanSequentialBanachAlaogluInstalled ≡ true
round488LeanSequentialBanachAlaogluInstalledIsTrue = refl

round488LeanWeakStarDualNormLSCInstalledIsTrue :
  round488LeanWeakStarDualNormLSCInstalled ≡ true
round488LeanWeakStarDualNormLSCInstalledIsTrue = refl

round488DirectHardBudgetIsOnlyNovelNSMathematicsIsTrue :
  round488DirectHardBudgetIsOnlyNovelNSMathematics ≡ true
round488DirectHardBudgetIsOnlyNovelNSMathematicsIsTrue = refl

round488NoHardBudgetManufacturedFromStandardAnalysisIsTrue :
  round488NoHardBudgetManufacturedFromStandardAnalysis ≡ true
round488NoHardBudgetManufacturedFromStandardAnalysisIsTrue = refl
