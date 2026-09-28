{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralS4SameObjectPackageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _≤_)
import Data.Rational.Properties as ℚP

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109FiniteHistoryExact as LiteralHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBetaDrivenDensityExact as LiteralDensity
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Convention
import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED S4 SAME-OBJECT PACKAGE
--
-- Critical path:
--
--   literal plaquette producer
--      -> UV-oriented CMP109 trajectory
--      -> literal finite beta split
--      -> inverse-square terminal history
--      -> beta-driven CMP122 density
--      -> canonical Row-A cap
--      -> physical SU(2) anomaly threshold.
--
-- P3's propositional-equality running-recursion carrier is deliberately NOT a
-- premise of this no-go package.  Bishop reals are used only for the physical
-- coefficient normalization, where their native setoid semantics are sufficient.
------------------------------------------------------------------------

record LiteralS4SameObjectPackage
    (plaquette : Plaquette.PhysicalRunningCouplingData Nat)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (literalHistory :
      LiteralHistory.LiteralPlaquetteCMP109FiniteHistory plaquette trajectory)
    (terminal :
      Terminal.LiteralPlaquetteTerminalHistory
        plaquette trajectory literalHistory)
    (density :
      LiteralDensity.LiteralPlaquetteBetaDrivenDensity
        plaquette trajectory literalHistory terminal)
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        (LiteralDensity.asBetaDrivenCompleteDensityInputs density)
        rowA smallFieldCap largeFieldCap covarianceCap

    traceBoundary :
      SU2Convention.CanonicalBishopSU2TraceBoundary

open LiteralS4SameObjectPackage public

literalBetaDrivenInputs :
  ∀ {plaquette trajectory literalHistory terminal density rowA
      smallFieldCap largeFieldCap covarianceCap} →
  LiteralS4SameObjectPackage
    plaquette trajectory literalHistory terminal density rowA
    smallFieldCap largeFieldCap covarianceCap →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory}
    {split = Terminal.compiledSplit literalHistory}
literalBetaDrivenInputs {density = density} package =
  LiteralDensity.asBetaDrivenCompleteDensityInputs density

betaHistoryIsLiteralTerminalHistory :
  ∀ {plaquette trajectory literalHistory terminal density rowA
      smallFieldCap largeFieldCap covarianceCap}
    (package :
      LiteralS4SameObjectPackage
        plaquette trajectory literalHistory terminal density rowA
        smallFieldCap largeFieldCap covarianceCap) →
  Beta.betaHistory (literalBetaDrivenInputs package)
  ≡ Terminal.asBetaSplitInverseSquareTerminalHistory terminal
betaHistoryIsLiteralTerminalHistory package = refl

sameLiteralHistoryGammaAtMostOne :
  ∀ {plaquette trajectory literalHistory terminal density rowA
      smallFieldCap largeFieldCap covarianceCap}
    (package :
      LiteralS4SameObjectPackage
        plaquette trajectory literalHistory terminal density rowA
        smallFieldCap largeFieldCap covarianceCap) →
  History.gamma
    (Terminal.asBetaSplitInverseSquareTerminalHistory terminal)
  ≤ 1ℚ
sameLiteralHistoryGammaAtMostOne {rowA = rowA} package =
  ℚP.≤-trans
    (RowAState.historyGammaBelowCanonicalRowA
      (betaCoordinates package))
    (RowA.canonicalQuarticResponseGammaAtMostOne rowA)

sameLiteralHistoryInverseThresholdAtLeastOne :
  ∀ {plaquette trajectory literalHistory terminal density rowA
      smallFieldCap largeFieldCap covarianceCap}
    (package :
      LiteralS4SameObjectPackage
        plaquette trajectory literalHistory terminal density rowA
        smallFieldCap largeFieldCap covarianceCap) →
  1ℚ ≤
  History.inverseThreshold
    (Terminal.asBetaSplitInverseSquareTerminalHistory terminal)
sameLiteralHistoryInverseThresholdAtLeastOne package =
  let
    history = Terminal.asBetaSplitInverseSquareTerminalHistory _
  in
  Unit.inverseThresholdAtLeastOneFromUnitCap
    (History.gammaPositive history)
    (sameLiteralHistoryGammaAtMostOne package)
    (History.inverseThresholdRepresentation history)

physicalSU2ThresholdBelowLiteralHistory :
  ∀ {plaquette trajectory literalHistory terminal density rowA
      smallFieldCap largeFieldCap covarianceCap}
    (package :
      LiteralS4SameObjectPackage
        plaquette trajectory literalHistory terminal density rowA
        smallFieldCap largeFieldCap covarianceCap) →
  Bishop._≤_
    Threshold.physicalSU2NoGoThreshold
    (Embed.embed
      (History.inverseThreshold
        (Terminal.asBetaSplitInverseSquareTerminalHistory terminal)))
physicalSU2ThresholdBelowLiteralHistory package =
  Threshold.historyAtLeastOneDominatesPhysicalSU2Threshold
    (sameLiteralHistoryInverseThresholdAtLeastOne package)

p3RunningRecursionRequiredForS4NoGo : Bool
p3RunningRecursionRequiredForS4NoGo = false

parallelBetaSplitRequired : Bool
parallelBetaSplitRequired = false

parallelBetaHistoryRequired : Bool
parallelBetaHistoryRequired = false

postHocRepositoryCapEqualityRequired : Bool
postHocRepositoryCapEqualityRequired = false

postHocPiNormalizationEqualityRequired : Bool
postHocPiNormalizationEqualityRequired = false

p3RunningRecursionRequiredForS4NoGoIsFalse :
  p3RunningRecursionRequiredForS4NoGo ≡ false
p3RunningRecursionRequiredForS4NoGoIsFalse = refl

parallelBetaSplitRequiredIsFalse :
  parallelBetaSplitRequired ≡ false
parallelBetaSplitRequiredIsFalse = refl

parallelBetaHistoryRequiredIsFalse :
  parallelBetaHistoryRequired ≡ false
parallelBetaHistoryRequiredIsFalse = refl

postHocRepositoryCapEqualityRequiredIsFalse :
  postHocRepositoryCapEqualityRequired ≡ false
postHocRepositoryCapEqualityRequiredIsFalse = refl

postHocPiNormalizationEqualityRequiredIsFalse :
  postHocPiNormalizationEqualityRequired ≡ false
postHocPiNormalizationEqualityRequiredIsFalse = refl

literalS4SameObjectCompilerLevel : ProofLevel
literalS4SameObjectCompilerLevel = machineChecked
