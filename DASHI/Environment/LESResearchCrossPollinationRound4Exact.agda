module DASHI.Environment.LESResearchCrossPollinationRound4Exact where

------------------------------------------------------------------------
-- ROUND 4: THEOREMS ACROSS THE EXTRACTED GENERIC KERNEL
--
-- Round 3 extracted common record shapes.  Round 4 closes several actual
-- theorem connections so that the shared kernel is not merely a vocabulary:
--
--   * exact causal abstraction -> generic intervention intertwiner;
--   * exact causal outcome abstraction -> consumer descent;
--   * LES hybrid execution -> a world-only instance of dual-effect action;
--   * the cross-domain regression exercises consumer-relative future safety,
--     selective authority, adaptive fidelity, proof-carrying composition and
--     provenance-root independence.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.DualEffectInformationActionExact as Dual
import DASHI.Core.ReopenableConsumerInterventionCrossDomainRegression as Regression
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Round2

------------------------------------------------------------------------
-- 1. Exact causal intervention abstraction is literally an intertwiner.
------------------------------------------------------------------------

causalInterventionAbstractionToIntertwiner :
  ∀ {LowState HighState LowIntervention HighIntervention LowOutcome HighOutcome}
    {low : Round2.CausalInterventionSystem LowState LowIntervention LowOutcome}
    {high : Round2.CausalInterventionSystem HighState HighIntervention HighOutcome}
    (abstraction : Round2.ExactCausalAbstraction low high)
    (intervention : LowIntervention) →
  Core.Intertwiner
    (Round2.stateMap abstraction)
    (Round2.stateMap abstraction)
    (Round2.intervene low intervention)
    (Round2.intervene high (Round2.interventionMap abstraction intervention))
causalInterventionAbstractionToIntertwiner abstraction intervention =
  Core.intertwiner
    (Round2.interventionSquareCommutes abstraction intervention)

------------------------------------------------------------------------
-- 2. Outcome abstraction is consumer descent through the state quotient/map.
--    The fine consumer is the low outcome followed by outcomeMap; the coarse
--    consumer is the high-level outcome.
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
-- 3. Hybrid execution is one world-dynamics instance of the dual-effect action
--    system.  Information is explicitly fixed; later active sensing can replace
--    the trivial information carrier without changing the action interface.
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
-- 4. Keep the concrete finite cross-domain falsifiers in the LES regression
-- ancestry.  This is a theorem import, not a prose status flag.
------------------------------------------------------------------------

consumerRelativityRegression :
  (depth : Agda.Builtin.Nat.Nat) →
  DASHI.Core.ConsumerIndexedGovernedTransitionExact.FutureEquivalent
    Regression.publicSystem Regression.public depth Regression.left Regression.right
consumerRelativityRegression = Regression.publicStatesEquivalentAtEveryRequestedDepth
