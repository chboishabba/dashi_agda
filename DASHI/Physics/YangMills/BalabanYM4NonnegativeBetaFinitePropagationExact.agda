module DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact where

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
-- Iterate the already checked one-step source-oriented monotonicity theorem.
-- With u_k = g_k^-2 and
--
--       u_k = u_{k+1} + beta_{k+1},      beta_{k+1} >= 0,
--
-- every coarser inverse coupling is no larger than every preceding finer one.
-- We use an explicit recursive advance(start,gap) rather than importing Nat
-- addition machinery, keeping this leaf lightweight for the Gate-4 Track-B
-- validation root.
--
-- This is exactly the order-theoretic fact needed to propagate a lower inverse-
-- coupling threshold at a terminal/coarser scale backwards through every UV
-- scale.  It does NOT prove beta>=0; that remains an analytic input.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4SourceCouplingSmallnessPropagationExact as Step

advance : Nat → Nat → Nat
advance start zero = start
advance start (suc gap) = suc (advance start gap)

inverseCouplingFiniteMonotone :
  ∀ {trajectory}
    (nonnegative : Step.NonnegativeBetaTrajectory trajectory)
    start gap →
  Flow.inverseCoupling trajectory (advance start gap)
  ≤ Flow.inverseCoupling trajectory start
inverseCouplingFiniteMonotone nonnegative start zero = ℚP.≤-refl
inverseCouplingFiniteMonotone {trajectory} nonnegative start (suc gap) =
  ℚP.≤-trans
    (Step.inverseCouplingNextBelowCurrent nonnegative (advance start gap))
    (inverseCouplingFiniteMonotone nonnegative start gap)

inverseThresholdPropagatesBackwards :
  ∀ {trajectory}
    (nonnegative : Step.NonnegativeBetaTrajectory trajectory)
    threshold start gap →
  threshold ≤ Flow.inverseCoupling trajectory (advance start gap) →
  threshold ≤ Flow.inverseCoupling trajectory start
inverseThresholdPropagatesBackwards nonnegative threshold start gap terminalThreshold =
  ℚP.≤-trans terminalThreshold
    (inverseCouplingFiniteMonotone nonnegative start gap)

ym4NonnegativeBetaFiniteMonotonicityLevel : ProofLevel
ym4NonnegativeBetaFiniteMonotonicityLevel = machineChecked

ym4InverseThresholdBackwardPropagationLevel : ProofLevel
ym4InverseThresholdBackwardPropagationLevel = machineChecked
