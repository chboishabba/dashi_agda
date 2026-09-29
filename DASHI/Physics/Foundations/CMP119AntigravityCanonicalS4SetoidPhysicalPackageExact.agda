{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SetoidPhysicalPackageExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _≤_)
import Data.Rational.Properties as ℚP

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalSignedQuarticReceiptExact as Signed
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptMajorantExact as ReceiptMajorant
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidRunningRecursionExact as Setoid
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor

------------------------------------------------------------------------
-- S4 setoid-native physical producer.
-- Owns the same CMP109 trajectory as the Row-A cap and the P3G state;
-- neither the old P3 recursionExact (_≡_) nor any edge-state splice occurs.
-- The plaquette coefficient weld and Gaussian projection remain explicit
-- provenance obligations.  Physical quantitative remainder control is
-- separately typed, never silently inferred from recurrence.
------------------------------------------------------------------------

record CanonicalS4SetoidPhysicalPackage
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    coefficientWeld :
      Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory

    rich :
      Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ

    geometry :
      Core.P3GSetoidPhysicalGeometry coefficientWeld rich

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

  running : Setoid.SetoidRunningCouplingRecursion Nat
  running = Setoid.fromPhysicalCore geometry

  sameSource :
    Setoid.SameSourceUVIncrement trajectory running
  sameSource = Setoid.physicalCoreSameSource geometry

  sameHistory :
    ∀ depth →
    Bishop._≃_
      (Setoid.inverseCouplingSq running depth)
      (Core.physicalState trajectory depth)
  sameHistory = Setoid.stateSameAtEveryDepth sameSource

open CanonicalS4SetoidPhysicalPackage public

sameHistoryGammaAtMostOne :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SetoidPhysicalPackage
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
      CanonicalS4SetoidPhysicalPackage
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
      CanonicalS4SetoidPhysicalPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  Bishop._≤_
    Threshold.physicalSU2NoGoThreshold
    (Embed.embed
      (History.inverseThreshold (BetaFlow.betaHistory inputs)))
physicalSU2ThresholdBelowSameHistory package =
  Threshold.historyAtLeastOneDominatesPhysicalSU2Threshold
    (sameHistoryInverseThresholdAtLeastOne package)

-- Optional *external* analytic estimate; no manufactured |R| ≤ |R|.
record CanonicalS4SetoidControlledRemainder
    {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SetoidPhysicalPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap)
    (majorant : Nat → Bishop.ℝ) : Set₁ where
  field
    sourceBound :
      Setoid.PhysicalRemainderMajorant (running package) majorant

-- Concrete quantitative S4 remainder producer from the SAME literal source.
-- The physical source must supply certified signed quartic and order receipts;
-- the majorant and its two-sided Bishop estimates are then computed, not
-- separately postulated.
controlledRemainderFromPhysicalReceipts :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package :
      CanonicalS4SetoidPhysicalPackage
        {trajectory = trajectory} {split = split}
        inputs rowA smallFieldCap largeFieldCap covarianceCap)
    (source : Signed.PhysicalSignedQuarticSource (geometry package)) →
  CanonicalS4SetoidControlledRemainder package
    (ReceiptMajorant.physicalReceiptMajorant source)
controlledRemainderFromPhysicalReceipts package source = record
  { CanonicalS4SetoidControlledRemainder.sourceBound =
      ReceiptMajorant.asPhysicalRemainderMajorant source
  }
