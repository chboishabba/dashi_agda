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
-- provided every earlier scale has a finite gap to that terminal scale.
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
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

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

    gapToTerminal : Nat → Nat
    scaleReachesTerminal : ∀ scale →
      Finite.advance scale (gapToTerminal scale) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold ≤ Flow.inverseCoupling trajectory terminalScale

    betaNonnegative : Step.NonnegativeBetaTrajectory trajectory

    inverseThresholdImpliesSmallCoupling : ∀ scale →
      inverseThreshold ≤ Flow.inverseCoupling trajectory scale →
      couplingAt scale ≤ gamma

open TerminalInverseThresholdHistory public

inverseThresholdAtEveryScale :
  ∀ {trajectory}
    (history : TerminalInverseThresholdHistory trajectory) scale →
  inverseThreshold history ≤ Flow.inverseCoupling trajectory scale
inverseThresholdAtEveryScale {trajectory} history scale =
  let
    terminalAsAdvance :
      inverseThreshold history
      ≤ Flow.inverseCoupling trajectory
          (Finite.advance scale (gapToTerminal history scale))
    terminalAsAdvance = subst
      (λ index →
        inverseThreshold history ≤ Flow.inverseCoupling trajectory index)
      (symmetry (scaleReachesTerminal history scale))
      (terminalInverseThreshold history)

    backward = Finite.inverseThresholdPropagatesBackwards
      (betaNonnegative history)
      (inverseThreshold history)
      scale
      (gapToTerminal history scale)
      terminalAsAdvance
  in backward
  where
  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

smallCouplingAtEveryScale :
  ∀ {trajectory}
    (history : TerminalInverseThresholdHistory trajectory) scale →
  couplingAt history scale ≤ gamma history
smallCouplingAtEveryScale history scale =
  inverseThresholdImpliesSmallCoupling history scale
    (inverseThresholdAtEveryScale history scale)

balabanTerminalInverseThresholdPropagationLevel : ProofLevel
balabanTerminalInverseThresholdPropagationLevel = machineChecked

balabanTerminalThresholdToSmallCouplingHistoryLevel : ProofLevel
balabanTerminalThresholdToSmallCouplingHistoryLevel = machineChecked

-- Remaining representation leaf: instantiate inverseThresholdImpliesSmallCoupling
-- for the literal positive rational relation u_k=1/g_k^2.  The RG-specific part
-- of the all-scale history is reduced to beta>=0 plus the terminal threshold.
balabanRationalInverseSquareOrderDictionaryLevel : ProofLevel
balabanRationalInverseSquareOrderDictionaryLevel = conditional
