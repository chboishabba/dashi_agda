module DASHI.Environment.LESResearchCrossPollinationRound5Exact where

------------------------------------------------------------------------
-- ROUND 5: CROSS-PROJECT THEOREM WELDS
--
-- Round 4 already closes the broad LES gap map.  This module adds the missing
-- theorem connections exposed specifically by SeaMeInIt / Animalexic / LES:
--
--   * causal outcome abstraction is consumer descent;
--   * hybrid execution is a world-only dual-effect action system;
--   * consumer-relative bounded future equivalence remains an executable
--     cross-domain regression rather than a prose boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Core.DualEffectInformationActionExact as Dual
import DASHI.Core.ReopenableConsumerInterventionCrossDomainRegression as Regression
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Round2
import DASHI.Environment.LESResearchCrossPollinationRound4Exact as Round4

------------------------------------------------------------------------
-- Outcome commutation is exactly consumer descent through the high-level state
-- map.  Round 4 already owns the intervention-intertwiner theorem.
------------------------------------------------------------------------

causalOutcomeAbstractionToConsumerDescent :
  ∀ {LowState HighState LowIntervention HighIntervention LowOutcome HighOutcome}
    {low : Round2.CausalInterventionSystem LowState LowIntervention LowOutcome}
    {high : Round2.CausalInterventionSystem HighState HighIntervention HighOutcome}
    (abstraction : Round2.ExactCausalAbstraction low high) →
  Core.ConsumerDescent
    (Round2.stateMap abstraction)
    (λ state →
      Round2.outcomeMap abstraction (Round2.observeOutcome low state))
causalOutcomeAbstractionToConsumerDescent {high = high} abstraction =
  Core.consumerDescent
    (Round2.observeOutcome high)
    (Round2.outcomeSquareCommutes abstraction)

------------------------------------------------------------------------
-- A hybrid LES command changes the physical/world coordinate and leaves a
-- trivial information coordinate fixed.  Later active sensing can replace the
-- unit information carrier without changing the action interface.
------------------------------------------------------------------------

hybridAsDualEffect :
  ∀ {Mode Continuous DiscreteAction} →
  Round2.HybridSystem Mode Continuous DiscreteAction →
  Dual.DualEffectAction
    (Round2.HybridState Mode Continuous)
    ⊤
    (Round2.HybridCommand Mode Continuous DiscreteAction)
hybridAsDualEffect system =
  Dual.dualEffectAction
    (Round2.hybridStep system)
    (λ command information → information)

hybridCommandsAreWorldOnly :
  ∀ {Mode Continuous DiscreteAction}
    (system : Round2.HybridSystem Mode Continuous DiscreteAction)
    (command : Round2.HybridCommand Mode Continuous DiscreteAction) →
  Dual.WorldOnly (hybridAsDualEffect system) command
hybridCommandsAreWorldOnly system command =
  Dual.worldOnly (λ information → refl)

------------------------------------------------------------------------
-- The bounded future-equivalence regression is retained at the LES review
-- surface, but its theorem owner remains the generic governed-transition core.
------------------------------------------------------------------------

consumerRelativityRegression :
  (depth : Nat) →
  Governed.FutureEquivalent
    Regression.publicSystem Regression.public depth Regression.left Regression.right
consumerRelativityRegression = Regression.publicStatesEquivalentAtEveryRequestedDepth

round5BuildsOnRound4 : Round4.LESRound4FormalClosureStatus
round5BuildsOnRound4 = Round4.canonicalLESRound4FormalClosureStatus
