module DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Eliminate the last parallel-trajectory loophole between the finite beta
-- calculation and CMP122 Theorem 1.  The source `Balaban1989EffectiveDensityFlow`
-- constructed here has
--
--       couplingAt k = the couplingAt k of the beta history
--
-- definitionally.  Its `allEffectiveCouplingsSmall` field is proved by the
-- beta-split/terminal inverse-square theorem, not supplied independently.
-- Thus a CMP122 theorem witness on this flow is literally conditioned on the
-- same couplings produced by the finite-lattice beta calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; Positive; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source

record BetaDrivenCompleteDensityInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory} : Set₁ where
  field
    Density : Set
    betaHistory : History.BetaSplitInverseSquareTerminalHistoryData trajectory split

    densityAt : Nat → Density
    InSection2DensityClass : Nat → Density → Set
    Section2ConditionsAndBounds : Nat → Density → Set

    -- The finite source trajectory tells us exactly which scales occur in the
    -- complete-density flow.
    sourceScaleActive : ∀ scale → History.ActiveScale betaHistory scale

open BetaDrivenCompleteDensityInputs public

betaDrivenCompleteDensityFlow :
  ∀ {trajectory split} →
  (inputs : BetaDrivenCompleteDensityInputs {trajectory} {split}) →
  Source.Balaban1989EffectiveDensityFlow ℚ (Density inputs)
betaDrivenCompleteDensityFlow inputs = record
  { Source.Balaban1989EffectiveDensityFlow.couplingAt =
      History.couplingAt (betaHistory inputs)
  ; Source.Balaban1989EffectiveDensityFlow.densityAt = densityAt inputs
  ; Source.Balaban1989EffectiveDensityFlow.Positive = Positive
  ; Source.Balaban1989EffectiveDensityFlow.LessEqual = _≤_
  ; Source.Balaban1989EffectiveDensityFlow.gamma =
      History.gamma (betaHistory inputs)
  ; Source.Balaban1989EffectiveDensityFlow.InSection2DensityClass =
      InSection2DensityClass inputs
  ; Source.Balaban1989EffectiveDensityFlow.Section2ConditionsAndBounds =
      Section2ConditionsAndBounds inputs
  ; Source.Balaban1989EffectiveDensityFlow.allEffectiveCouplingsSmall =
      λ scale _ →
        History.smallCouplingAtEveryActiveScale
          (betaHistory inputs) scale (sourceScaleActive inputs scale)
  ; Source.Balaban1989EffectiveDensityFlow.allEffectiveCouplingsPositive =
      History.couplingPositive (betaHistory inputs)
  }

sourceCouplingIsBetaHistoryCoupling :
  ∀ {trajectory split}
    (inputs : BetaDrivenCompleteDensityInputs {trajectory} {split}) scale →
  Source.couplingAt (betaDrivenCompleteDensityFlow inputs) scale
  ≡ History.couplingAt (betaHistory inputs) scale
sourceCouplingIsBetaHistoryCoupling inputs scale = refl

sourceSmallnessIsDerivedFromBetaHistory :
  ∀ {trajectory split}
    (inputs : BetaDrivenCompleteDensityInputs {trajectory} {split}) scale →
  Source.LessEqual (betaDrivenCompleteDensityFlow inputs)
    (Source.couplingAt (betaDrivenCompleteDensityFlow inputs) scale)
    (Source.gamma (betaDrivenCompleteDensityFlow inputs))
sourceSmallnessIsDerivedFromBetaHistory inputs scale =
  History.smallCouplingAtEveryActiveScale
    (betaHistory inputs) scale (sourceScaleActive inputs scale)

balabanBetaDrivenSourceFlowLevel : ProofLevel
balabanBetaDrivenSourceFlowLevel = machineChecked

balabanBetaHistoryIsLiteralCMP122CouplingLevel : ProofLevel
balabanBetaHistoryIsLiteralCMP122CouplingLevel = machineChecked
