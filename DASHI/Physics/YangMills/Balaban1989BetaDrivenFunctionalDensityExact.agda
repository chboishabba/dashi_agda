module DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact where

------------------------------------------------------------------------
-- BETA-DRIVEN CMP119 DENSITY ON ITS LITERAL FUNCTIONAL CARRIER
--
-- A source effective density is a function of the selected gauge/background
-- configuration.  The historical beta-flow kept Density opaque and later had
-- to postulate an evaluator.  This preferred route fixes
--
--   Density = SlowField -> ℝ
--
-- at construction time.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
import Data.Nat.Base as N
open import Data.Rational.Base using (ℚ)
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta

record BetaDrivenFunctionalDensityInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (SlowField : Set) : Set₁ where
  field
    betaHistory :
      History.BetaSplitInverseSquareTerminalHistoryData trajectory split

    densityAt : Nat → SlowField → ℝ

    InSection2DensityClass :
      Nat → (SlowField → ℝ) → Set

    Section2ConditionsAndBounds :
      Nat → (SlowField → ℝ) → Set

    sourceScaleActive :
      ∀ scale → History.ActiveScale betaHistory scale

open BetaDrivenFunctionalDensityInputs public

asBetaDrivenCompleteDensityInputs :
  ∀ {trajectory split SlowField} →
  BetaDrivenFunctionalDensityInputs
    {trajectory = trajectory} {split = split} SlowField →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory} {split = split}
asBetaDrivenCompleteDensityInputs inputs = record
  { Beta.BetaDrivenCompleteDensityInputs.Density =
      SlowField → ℝ
  ; Beta.BetaDrivenCompleteDensityInputs.betaHistory =
      betaHistory inputs
  ; Beta.BetaDrivenCompleteDensityInputs.densityAt =
      densityAt inputs
  ; Beta.BetaDrivenCompleteDensityInputs.InSection2DensityClass =
      InSection2DensityClass inputs
  ; Beta.BetaDrivenCompleteDensityInputs.Section2ConditionsAndBounds =
      Section2ConditionsAndBounds inputs
  ; Beta.BetaDrivenCompleteDensityInputs.sourceScaleActive =
      sourceScaleActive inputs
  }

functionalDensityIsLiteralFunctionLevel : ProofLevel
functionalDensityIsLiteralFunctionLevel = machineChecked

functionalDensityBetaFlowCompilerLevel : ProofLevel
functionalDensityBetaFlowCompilerLevel = machineChecked

-- Preferred finite physical entry point, independent of the impossible
-- historical all-Nat record. The functional carrier is unchanged.
module _
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (h : History.BetaSplitInverseSquareTerminalHistoryData trajectory split)
    (coverage : ∀ k → k N.≤ History.terminalScale h → History.ActiveScale h k)
    {SlowField : Set}
    (density : Nat → SlowField → ℝ)
    (form bounds : Nat → (SlowField → ℝ) → Set)
  where

  finiteFunctionalDensityFlow :
    Source.Balaban1989EffectiveDensityFlow ℚ (SlowField → ℝ)
  finiteFunctionalDensityFlow =
    Beta.finiteBetaDrivenCompleteDensityFlow h coverage density form bounds

  finiteFunctionalDensityAgrees : ∀ k →
    k N.≤ History.terminalScale h →
    Source.densityAt finiteFunctionalDensityFlow k ≡ density k
  finiteFunctionalDensityAgrees =
    Beta.finiteDensityAgreesOnPhysicalScale h coverage density form bounds

  finiteFunctionalCouplingAgrees : ∀ k →
    k N.≤ History.terminalScale h →
    Source.couplingAt finiteFunctionalDensityFlow k ≡ History.couplingAt h k
  finiteFunctionalCouplingAgrees =
    Beta.finiteCouplingAgreesOnPhysicalScale h coverage density form bounds
