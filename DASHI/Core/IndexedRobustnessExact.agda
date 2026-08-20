module DASHI.Core.IndexedRobustnessExact where

------------------------------------------------------------------------
-- UNCERTAINTY-INDEXED ROBUSTNESS
--
-- Robustness to pose, material, sensor, model, scenario, semantic ambiguity or
-- manufacturing tolerance are different obligations.  This module keeps the
-- axis in the type and proves a simple tagged-union composition theorem rather
-- than scalarising heterogeneous robustness claims.
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)

record RobustAcross
    (Candidate Axis Scenario : Set)
    (Accept : Candidate → Axis → Scenario → Set)
    (candidate : Candidate)
    (axis : Axis) : Set₁ where
  constructor robustAcross
  field
    DeclaredScenario : Scenario → Set
    robust :
      ∀ scenario → DeclaredScenario scenario →
      Accept candidate axis scenario

open RobustAcross public

------------------------------------------------------------------------
-- Two scenario families on the same candidate/axis may be joined without
-- inventing a probability mixture.  The result is robustness over the tagged
-- disjoint union of the declared scenarios.
------------------------------------------------------------------------

joinRobustScenarioFamilies :
  ∀ {Candidate Axis ScenarioA ScenarioB}
    {AcceptA : Candidate → Axis → ScenarioA → Set}
    {AcceptB : Candidate → Axis → ScenarioB → Set}
    {candidate : Candidate} {axis : Axis} →
  RobustAcross Candidate Axis ScenarioA AcceptA candidate axis →
  RobustAcross Candidate Axis ScenarioB AcceptB candidate axis →
  RobustAcross
    Candidate Axis (ScenarioA ⊎ ScenarioB)
    (λ c a scenario →
      caseAccept c a scenario)
    candidate axis
  where
    caseAccept :
      Candidate → Axis → ScenarioA ⊎ ScenarioB → Set
    caseAccept c a (inj₁ scenario) = AcceptA c a scenario
    caseAccept c a (inj₂ scenario) = AcceptB c a scenario
joinRobustScenarioFamilies left right =
  robustAcross declared robustJoined
  where
    declared : _
    declared (inj₁ scenario) = DeclaredScenario left scenario
    declared (inj₂ scenario) = DeclaredScenario right scenario

    robustJoined :
      ∀ scenario → declared scenario → _
    robustJoined (inj₁ scenario) declaredHere = robust left scenario declaredHere
    robustJoined (inj₂ scenario) declaredHere = robust right scenario declaredHere

------------------------------------------------------------------------
-- The theorem above composes declared sets only.  It does not say robustness
-- on one axis implies robustness on another axis, nor infer probabilities.
------------------------------------------------------------------------
