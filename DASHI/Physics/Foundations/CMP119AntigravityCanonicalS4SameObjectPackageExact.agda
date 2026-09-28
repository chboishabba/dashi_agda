{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _≤_)
import Data.Rational.Properties as ℚP

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Convention
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact as Running
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL S4 SAME-OBJECT PACKAGE
--
-- One object now owns:
--   * the literal rational CMP109/CMP119 beta history;
--   * the canonical Row-A cap used by that state;
--   * the Bishop SU(2) running convention with Machin pi^{-2};
--   * the Lorentzian trace boundary with the same pi^{-2};
--   * the exact UV-directed rational->Bishop history representation.
--
-- The only non-compiler bridge left here is the physically meaningful claim
-- that the Bishop P3 recursion really is the embedded CMP109 source history.
------------------------------------------------------------------------

record CanonicalS4SameObjectPackage
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning :
      SU2Convention.CanonicalBishopSU2RunningInputs Nat

    bishopRunningRepresentsCMP109History :
      UV.P3RepresentsSourceUVView
        trajectory
        (SU2Convention.recursion bishopRunning)

    traceBoundary :
      SU2Convention.CanonicalBishopSU2TraceBoundary

open CanonicalS4SameObjectPackage public

sameHistoryGammaAtMostOne :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SameObjectPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  History.gamma (BetaFlow.betaHistory inputs) ≤ 1ℚ
sameHistoryGammaAtMostOne {rowA = rowA} package =
  ℚP.≤-trans
    (RowAState.historyGammaBelowCanonicalRowA
      (betaCoordinates package))
    (RowA.canonicalQuarticResponseGammaAtMostOne rowA)

sameHistoryInverseThresholdAtLeastOne :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SameObjectPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  1ℚ ≤ History.inverseThreshold (BetaFlow.betaHistory inputs)
sameHistoryInverseThresholdAtLeastOne {inputs = inputs} package =
  Unit.inverseThresholdAtLeastOneFromUnitCap
    (History.gammaPositive (BetaFlow.betaHistory inputs))
    (sameHistoryGammaAtMostOne package)
    (History.inverseThresholdRepresentation (BetaFlow.betaHistory inputs))

physicalSU2ThresholdBelowSameHistory :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SameObjectPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  Bishop._≤_
    Threshold.physicalSU2NoGoThreshold
    (Embed.embed
      (History.inverseThreshold (BetaFlow.betaHistory inputs)))
physicalSU2ThresholdBelowSameHistory package =
  Threshold.historyAtLeastOneDominatesPhysicalSU2Threshold
    (sameHistoryInverseThresholdAtLeastOne package)

sameRunningPiIsThresholdPi :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SameObjectPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  Running.inversePiSquared
    (SU2Convention.canonicalBishopSU2RunningConvention
      (bishopRunning package))
  ≡
  DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact.inversePiSquared
sameRunningPiIsThresholdPi package = refl

postHocCapEqualityRequired : Bool
postHocCapEqualityRequired = false

postHocPiConventionEqualityRequired : Bool
postHocPiConventionEqualityRequired = false

p3HistorySameObjectWitnessStillRequired : Bool
p3HistorySameObjectWitnessStillRequired = true

postHocCapEqualityRequiredIsFalse :
  postHocCapEqualityRequired ≡ false
postHocCapEqualityRequiredIsFalse = refl

postHocPiConventionEqualityRequiredIsFalse :
  postHocPiConventionEqualityRequired ≡ false
postHocPiConventionEqualityRequiredIsFalse = refl

p3HistorySameObjectWitnessStillRequiredIsTrue :
  p3HistorySameObjectWitnessStillRequired ≡ true
p3HistorySameObjectWitnessStillRequiredIsTrue = refl

canonicalS4SameObjectCompilerLevel : ProofLevel
canonicalS4SameObjectCompilerLevel = machineChecked

literalP3CMP109SameObjectIdentificationLevel : ProofLevel
literalP3CMP109SameObjectIdentificationLevel = conditional
