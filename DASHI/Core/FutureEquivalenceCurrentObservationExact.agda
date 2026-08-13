module DASHI.Core.FutureEquivalenceCurrentObservationExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- FULL FUTURE EQUIVALENCE REFINES PRESENT OBSERVATION EQUALITY
--
-- The empty trace is part of the future language.  Hence two states with the
-- same complete consumer-visible future language must already agree under the
-- present observation.  The converse need not hold (hidden phase, telescope,
-- grokking, LSTM and neural-bottleneck counterexamples instantiate failure).
------------------------------------------------------------------------

currentObservationWitness :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    (state : State) →
  Future.FutureObservation system project state [] (project state)
currentObservationWitness state =
  Future.futureObservation state Reachability.executesNil refl

futureEquivalentImpliesCurrentObservationEqual :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {left right : State} →
  Future.FutureObservationEquivalent system project left right →
  project left ≡ project right
futureEquivalentImpliesCurrentObservationEqual
  {project = project} {left = left} {right = right} equivalent
  with Future.forward
    (Future.sameFutureLanguage equivalent [] (project left))
    (currentObservationWitness left)
... | Future.futureObservation .right Reachability.executesNil observationProof =
  sym observationProof

------------------------------------------------------------------------
-- This theorem supplies one inclusion in the observational hierarchy:
-- canonical future equivalence is always at least as discriminating as the
-- present-observation quotient.
------------------------------------------------------------------------
