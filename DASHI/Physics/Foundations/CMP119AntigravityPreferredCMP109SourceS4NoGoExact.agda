{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredCMP109SourceS4NoGoExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; _≤_)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceCouplingExact as A2Source
import DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceTerminalGeometryExact as A2Geometry
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowATerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowABetaDrivenDensityExact as Density
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Convention
import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact as CanonicalThreshold
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED S4: PRIMARY CMP109 SOURCE COUPLING + A2 CANONICAL ROW-A CAP
--
-- Provenance spine:
--
--   CMP109 trajectory owns u_k
--   CMP109SourceCouplingCoordinate owns g_k and u_k g_k^2 = 1
--   A2CMP109SourceCouplingCoordinate identifies the Row-A/A2 coupling with g_k
--   A2's existing cap is definitionally its canonical Row-A gamma
--   canonical reciprocal constructs u_* = gamma^-2
--   corrected beta history consumes exactly the same g_k
--
-- Coefficient/remainder coupling is NOT a premise of the terminal no-go.
------------------------------------------------------------------------

record PreferredCMP109SourceS4NoGo
    {HistoryCarrier Cell : Set}
    {cutoff : Agda.Builtin.Nat.Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (finiteHistory : FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (sourceCoupling : SourceCoupling.CMP109SourceCouplingCoordinate trajectory)
    (a2Coupling :
      A2Source.A2CMP109SourceCouplingCoordinate present sourceCoupling)
    (geometry :
      A2Geometry.A2CMP109SourceTerminalGeometry
        present finiteHistory sourceCoupling a2Coupling) : Set₂ where
  field
    density :
      Density.CMP109SourceRowABetaDrivenDensity
        finiteHistory
        sourceCoupling
        (Unified.rowAConstantsFromA2 present)
        (A2Geometry.asCMP109SourceRowATerminalGeometry geometry)

    traceBoundary :
      SU2Convention.CanonicalBishopSU2TraceBoundary

open PreferredCMP109SourceS4NoGo public

rowA :
  ∀ {HistoryCarrier Cell cutoff}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff) →
  RowA.FiniteQuarticResponseConstants
rowA = Unified.rowAConstantsFromA2

terminalHistory :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry} →
  PreferredCMP109SourceS4NoGo
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present trajectory weld finiteHistory sourceCoupling a2Coupling geometry →
  History.BetaSplitInverseSquareTerminalHistoryData
    trajectory
    (FiniteHistory.repositoryBetaSplit finiteHistory)
terminalHistory {geometry = geometry} package =
  Terminal.asBetaSplitInverseSquareTerminalHistory
    (A2Geometry.asCMP109SourceRowATerminalGeometry geometry)

betaDrivenInputs :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry} →
  PreferredCMP109SourceS4NoGo
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present trajectory weld finiteHistory sourceCoupling a2Coupling geometry →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory}
    {split = FiniteHistory.repositoryBetaSplit finiteHistory}
betaDrivenInputs package =
  Density.asBetaDrivenCompleteDensityInputs (density package)

betaHistoryUsesPrimaryCMP109SourceCoupling :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry}
    (package :
      PreferredCMP109SourceS4NoGo
        {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
        present trajectory weld finiteHistory sourceCoupling a2Coupling geometry)
    scale →
  History.couplingAt (Beta.betaHistory (betaDrivenInputs package)) scale
  ≡ SourceCoupling.sourceCoupling sourceCoupling scale
betaHistoryUsesPrimaryCMP109SourceCoupling package scale = refl

historyGammaIsA2CanonicalRowA :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry}
    (package :
      PreferredCMP109SourceS4NoGo
        {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
        present trajectory weld finiteHistory sourceCoupling a2Coupling geometry) →
  History.gamma (Beta.betaHistory (betaDrivenInputs package))
  ≡ RowA.canonicalQuarticResponseGamma (rowA present)
historyGammaIsA2CanonicalRowA package = refl

historyInverseThresholdIsCanonicalReciprocal :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry}
    (package :
      PreferredCMP109SourceS4NoGo
        {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
        present trajectory weld finiteHistory sourceCoupling a2Coupling geometry) →
  History.inverseThreshold (Beta.betaHistory (betaDrivenInputs package))
  ≡ CanonicalThreshold.canonicalInverseThreshold (rowA present)
historyInverseThresholdIsCanonicalReciprocal package = refl

sameHistoryInverseThresholdAtLeastOne :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry}
    (package :
      PreferredCMP109SourceS4NoGo
        {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
        present trajectory weld finiteHistory sourceCoupling a2Coupling geometry) →
  1ℚ ≤ CanonicalThreshold.canonicalInverseThreshold (rowA present)
sameHistoryInverseThresholdAtLeastOne {present = present} package =
  Unit.inverseThresholdAtLeastOneFromUnitCap
    (RowA.canonicalQuarticResponseGammaPositive (rowA present))
    (RowA.canonicalQuarticResponseGammaAtMostOne (rowA present))
    (CanonicalThreshold.canonicalInverseThresholdRepresentation (rowA present))

physicalSU2ThresholdBelowSameCMP109History :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling a2Coupling geometry}
    (package :
      PreferredCMP109SourceS4NoGo
        {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
        present trajectory weld finiteHistory sourceCoupling a2Coupling geometry) →
  Bishop._≤_
    Threshold.physicalSU2NoGoThreshold
    (Embed.embed (CanonicalThreshold.canonicalInverseThreshold (rowA present)))
physicalSU2ThresholdBelowSameCMP109History package =
  Threshold.historyAtLeastOneDominatesPhysicalSU2Threshold
    (sameHistoryInverseThresholdAtLeastOne package)

coefficientCouplingRequiredForTerminalNoGo : Bool
coefficientCouplingRequiredForTerminalNoGo = false

freeRowAConstantsRequired : Bool
freeRowAConstantsRequired = false

freeTerminalThresholdRequired : Bool
freeTerminalThresholdRequired = false

postDensityA2CouplingWeldRequired : Bool
postDensityA2CouplingWeldRequired = false

coefficientCouplingRequiredForTerminalNoGoIsFalse :
  coefficientCouplingRequiredForTerminalNoGo ≡ false
coefficientCouplingRequiredForTerminalNoGoIsFalse = refl

freeRowAConstantsRequiredIsFalse :
  freeRowAConstantsRequired ≡ false
freeRowAConstantsRequiredIsFalse = refl

freeTerminalThresholdRequiredIsFalse :
  freeTerminalThresholdRequired ≡ false
freeTerminalThresholdRequiredIsFalse = refl

postDensityA2CouplingWeldRequiredIsFalse :
  postDensityA2CouplingWeldRequired ≡ false
postDensityA2CouplingWeldRequiredIsFalse = refl

preferredCMP109SourceS4CompilerLevel : ProofLevel
preferredCMP109SourceS4CompilerLevel = machineChecked
