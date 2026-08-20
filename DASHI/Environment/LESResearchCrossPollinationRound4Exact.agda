module DASHI.Environment.LESResearchCrossPollinationRound4Exact where

------------------------------------------------------------------------
-- ROUND 4: THEOREMS ACROSS THE EXTRACTED GENERIC KERNEL
--
-- Round 3 extracted common record shapes.  Round 4 closes several actual
-- theorem connections so that the shared kernel is not merely a vocabulary:
-- exact causal abstraction -> generic intervention intertwiner; outcome
-- abstraction -> consumer descent; LES hybrid execution -> world-only
-- dual-effect action; concrete cross-domain regressions remain theorem-bearing.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Core.DualEffectInformationActionExact as Dual
import DASHI.Core.ReopenableConsumerInterventionCrossDomainRegression as Regression
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Round2

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

consumerRelativityRegression :
  (depth : Nat) →
  Governed.FutureEquivalent
    Regression.publicSystem Regression.public depth Regression.left Regression.right
consumerRelativityRegression = Regression.publicStatesEquivalentAtEveryRequestedDepth
