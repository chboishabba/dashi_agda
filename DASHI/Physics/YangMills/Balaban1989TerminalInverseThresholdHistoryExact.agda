module DASHI.Physics.YangMills.Balaban1989TerminalInverseThresholdHistoryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Localize the coupling-history hypothesis needed by CMP122 Theorem 1.
-- Because u_k=g_k^-2 decreases toward the coarser lattice whenever beta>=0,
-- it is enough to certify ONE inverse-coupling threshold at the terminal scale,
-- provided every ACTIVE earlier scale has a finite gap to that terminal scale.
--
-- The explicit ActiveScale predicate is essential: a finite RG trajectory has
-- no nonnegative gap from scales beyond its terminal index.  Thus this theorem
-- does not smuggle in an impossible all-Nat reachability hypothesis.
--
-- The only representation-specific input retained here is the elementary
-- monotone conversion
--
--       inverseThreshold <= u_k  =>  g_k <= gamma.
--
-- For a literal positive rational u_k=1/g_k^2 this is an order theorem, not RG
-- analysis.  Keeping it explicit prevents the direction of the inverse-square
-- comparison from being silently reversed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4SourceCouplingSmallnessPropagationExact as Step
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite

record TerminalInverseThresholdHistory
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    couplingAt : Nat → ℚ
    gamma inverseThreshold : ℚ
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold ≤ Flow.inverseCoupling trajectory terminalScale

    betaNonnegative : Step.NonnegativeBetaTrajectory trajectory

    inverseThresholdImpliesSmallCoupling : ∀ scale →
      inverseThreshold ≤ Flow.inverseCoupling trajectory scale →
      couplingAt scale ≤ gamma

open TerminalInverseThresholdHistory public

inverseThresholdAtActiveScale :
  ∀ {trajectory}
    (history : TerminalInverseThresholdHistory trajectory)
    scale → ActiveScale history scale →
  inverseThreshold history ≤ Flow.inverseCoupling trajectory scale
inverseThresholdAtActiveScale {trajectory} history scale active =
  let
    gap = gapToTerminal history scale active

    terminalAsAdvance :
      inverseThreshold history
      ≤ Flow.inverseCoupling trajectory (Finite.advance scale gap)
    terminalAsAdvance = subst
      (λ index →
        inverseThreshold history ≤ Flow.inverseCoupling trajectory index)
      (sym (scaleReachesTerminal history scale active))
      (terminalInverseThreshold history)
  in
  Finite.inverseThresholdPropagatesBackwards
    (betaNonnegative history)
    (inverseThreshold history)
    scale gap terminalAsAdvance

smallCouplingAtActiveScale :
  ∀ {trajectory}
    (history : TerminalInverseThresholdHistory trajectory)
    scale → ActiveScale history scale →
  couplingAt history scale ≤ gamma history
smallCouplingAtActiveScale history scale active =
  inverseThresholdImpliesSmallCoupling history scale
    (inverseThresholdAtActiveScale history scale active)

balabanTerminalInverseThresholdPropagationLevel : ProofLevel
balabanTerminalInverseThresholdPropagationLevel = machineChecked

balabanTerminalThresholdToSmallCouplingHistoryLevel : ProofLevel
balabanTerminalThresholdToSmallCouplingHistoryLevel = machineChecked

-- Remaining representation leaf: instantiate inverseThresholdImpliesSmallCoupling
-- for the literal positive rational relation u_k=1/g_k^2.  The RG-specific part
-- of the active all-scale history is reduced to beta>=0 plus one terminal
-- inverse threshold.
balabanRationalInverseSquareOrderDictionaryLevel : ProofLevel
balabanRationalInverseSquareOrderDictionaryLevel = conditional
