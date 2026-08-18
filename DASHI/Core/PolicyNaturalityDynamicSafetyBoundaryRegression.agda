module DASHI.Core.PolicyNaturalityDynamicSafetyBoundaryRegression where

------------------------------------------------------------------------
-- ADVERSARIAL REGRESSION
--
-- The existing PolicyRelativeProjectionSafety demo has a coarse Boolean
-- observer whose always-hold policy is policy-safe, even though an admissible
-- reveal action proves the projection dynamically unsafe.
--
-- Here the fine observer is simply the complete DemoState.  The coarse
-- observation factors exactly through it and the coarse policy lifts with a
-- perfect commuting action square.  The old dynamic defect nevertheless
-- remains.  Thus policy naturality is real structure, but not a substitute for
-- future-language/dynamic safety.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.PolicyObserverFactorizationNaturalityExact as Naturality
import DASHI.Core.PolicyRelativeProjectionSafety as Policy

fineDemoObserver : Policy.DemoState → Policy.DemoState
fineDemoObserver state = state

demoProjectionFactorsThroughFineState :
  Factorized.FactorizedRefinement
    Policy.demoProject
    fineDemoObserver
demoProjectionFactorsThroughFineState =
  Factorized.factorizedRefinement Policy.demoProject (λ state → refl)

liftedDemoPolicy :
  Policy.CoarseInterventionPolicy Policy.DemoState Policy.DemoAction
liftedDemoPolicy =
  Naturality.liftPolicyAlongFactorizedRefinement
    demoProjectionFactorsThroughFineState
    Policy.demoPolicy

liftedDemoPolicySelectsSameAction :
  (state : Policy.DemoState) →
  Policy.chooseAction liftedDemoPolicy (fineDemoObserver state)
  ≡ Policy.chooseAction Policy.demoPolicy (Policy.demoProject state)
liftedDemoPolicySelectsSameAction =
  Naturality.liftedPolicyNaturality
    demoProjectionFactorsThroughFineState
    Policy.demoPolicy

coarseDynamicDefectSurvivesPerfectPolicyNaturality :
  DASHI.Core.DynamicalQuotientSafety.TerminalisationDefect
    Policy.demoSystem
    Policy.demoProject
coarseDynamicDefectSurvivesPerfectPolicyNaturality = Policy.demoDynamicDefect

coarsePolicySafetyAlsoSurvives :
  Policy.PolicyRelativeSafety
    Policy.demoSystem
    Policy.demoProject
    Policy.demoPolicy
coarsePolicySafetyAlsoSurvives = Policy.demoPolicyIsSafe

record PolicyNaturalityWithoutDynamicSafetyWitness : Set₁ where
  constructor policyNaturalityWithoutDynamicSafetyWitness
  field
    factorizedObservation :
      Factorized.FactorizedRefinement
        Policy.demoProject
        fineDemoObserver
    exactActionNaturality :
      (state : Policy.DemoState) →
      Policy.chooseAction liftedDemoPolicy (fineDemoObserver state)
      ≡ Policy.chooseAction Policy.demoPolicy (Policy.demoProject state)
    coarsePolicySafe :
      Policy.PolicyRelativeSafety
        Policy.demoSystem
        Policy.demoProject
        Policy.demoPolicy
    unrestrictedDynamicDefect :
      DASHI.Core.DynamicalQuotientSafety.TerminalisationDefect
        Policy.demoSystem
        Policy.demoProject

canonicalPolicyNaturalityWithoutDynamicSafetyWitness :
  PolicyNaturalityWithoutDynamicSafetyWitness
canonicalPolicyNaturalityWithoutDynamicSafetyWitness =
  policyNaturalityWithoutDynamicSafetyWitness
    demoProjectionFactorsThroughFineState
    liftedDemoPolicySelectsSameAction
    Policy.demoPolicyIsSafe
    Policy.demoDynamicDefect
