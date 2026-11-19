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
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (z≤n; s≤s)
import Data.Nat.Base as N
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst)
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
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

------------------------------------------------------------------------
-- Finite physical scale correction. Preserve the historical ABI for its
-- consumers, but reject its impossible all-Nat activity premise.
------------------------------------------------------------------------

rightSuccessor : ∀ {m n} → m N.≤ n → m N.≤ suc n
rightSuccessor z≤n = z≤n
rightSuccessor (s≤s p) = s≤s (rightSuccessor p)

natReflexive : ∀ n → n N.≤ n
natReflexive zero = z≤n
natReflexive (suc n) = s≤s (natReflexive n)

advanceNeverDecreases : ∀ start gap → start N.≤ Finite.advance start gap
advanceNeverDecreases start zero = natReflexive start
advanceNeverDecreases start (suc gap) =
  rightSuccessor (advanceNeverDecreases start gap)

successorNotBelowSelf : ∀ n → suc n N.≤ n → ⊥
successorNotBelowSelf zero ()
successorNotBelowSelf (suc n) (s≤s p) = successorNotBelowSelf n p

legacyAllScalesActiveImpossible :
  ∀ {trajectory split} →
  BetaDrivenCompleteDensityInputs {trajectory} {split} → ⊥
legacyAllScalesActiveImpossible inputs =
  let
    h = betaHistory inputs
    K = History.terminalScale h
    active = sourceScaleActive inputs (suc K)
  in
  successorNotBelowSelf K
    (subst (λ end → suc K N.≤ end)
      (History.scaleReachesTerminal h (suc K) active)
      (advanceNeverDecreases (suc K)
        (History.gapToTerminal h (suc K) active)))

-- Terminal padding is only a total-index compatibility presentation:
-- no additional physical RG steps are asserted beyond K.
finiteScaleIndex : Nat → Nat → Nat
finiteScaleIndex zero K = zero
finiteScaleIndex (suc k) zero = zero
finiteScaleIndex (suc k) (suc K) = suc (finiteScaleIndex k K)

finiteScaleIndexWithinTerminal : ∀ k K → finiteScaleIndex k K N.≤ K
finiteScaleIndexWithinTerminal zero K = z≤n
finiteScaleIndexWithinTerminal (suc k) zero = z≤n
finiteScaleIndexWithinTerminal (suc k) (suc K) =
  s≤s (finiteScaleIndexWithinTerminal k K)

finiteScaleIndexKeepsActive : ∀ {k K} →
  k N.≤ K → finiteScaleIndex k K ≡ k
finiteScaleIndexKeepsActive {zero} p = refl
finiteScaleIndexKeepsActive {suc k} {suc K} (s≤s p)
  rewrite finiteScaleIndexKeepsActive p = refl

module _
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (h : History.BetaSplitInverseSquareTerminalHistoryData trajectory split)
    (coverage : ∀ k → k N.≤ History.terminalScale h → History.ActiveScale h k)
    {D : Set}
    (density : Nat → D)
    (form bounds : Nat → D → Set)
  where

  selectedFiniteScale : Nat → Nat
  selectedFiniteScale k = finiteScaleIndex k (History.terminalScale h)

  selectedFiniteScaleActive : ∀ k → History.ActiveScale h (selectedFiniteScale k)
  selectedFiniteScaleActive k =
    coverage (selectedFiniteScale k)
      (finiteScaleIndexWithinTerminal k (History.terminalScale h))

  -- Both coupling and density and BOTH source predicates are reindexed
  -- together. This does not extend the published physical trajectory.
  finiteBetaDrivenCompleteDensityFlow :
    Source.Balaban1989EffectiveDensityFlow ℚ D
  finiteBetaDrivenCompleteDensityFlow = record
    { Source.Balaban1989EffectiveDensityFlow.couplingAt =
        λ k → History.couplingAt h (selectedFiniteScale k)
    ; Source.Balaban1989EffectiveDensityFlow.densityAt =
        λ k → density (selectedFiniteScale k)
    ; Source.Balaban1989EffectiveDensityFlow.Positive = Positive
    ; Source.Balaban1989EffectiveDensityFlow.LessEqual = _≤_
    ; Source.Balaban1989EffectiveDensityFlow.gamma = History.gamma h
    ; Source.Balaban1989EffectiveDensityFlow.InSection2DensityClass =
        λ k → form (selectedFiniteScale k)
    ; Source.Balaban1989EffectiveDensityFlow.Section2ConditionsAndBounds =
        λ k → bounds (selectedFiniteScale k)
    ; Source.Balaban1989EffectiveDensityFlow.allEffectiveCouplingsSmall =
        λ k _ → History.smallCouplingAtEveryActiveScale h
          (selectedFiniteScale k) (selectedFiniteScaleActive k)
    ; Source.Balaban1989EffectiveDensityFlow.allEffectiveCouplingsPositive =
        λ k → History.couplingPositive h (selectedFiniteScale k)
    }

  finiteCouplingAgreesOnPhysicalScale : ∀ k →
    k N.≤ History.terminalScale h →
    Source.couplingAt finiteBetaDrivenCompleteDensityFlow k ≡ History.couplingAt h k
  finiteCouplingAgreesOnPhysicalScale k active
    rewrite finiteScaleIndexKeepsActive active = refl

  finiteDensityAgreesOnPhysicalScale : ∀ k →
    k N.≤ History.terminalScale h →
    Source.densityAt finiteBetaDrivenCompleteDensityFlow k ≡ density k
  finiteDensityAgreesOnPhysicalScale k active
    rewrite finiteScaleIndexKeepsActive active = refl
