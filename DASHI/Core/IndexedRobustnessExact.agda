module DASHI.Core.IndexedRobustnessExact where

------------------------------------------------------------------------
-- UNCERTAINTY-INDEXED ROBUSTNESS
-- Robustness to pose, material, sensor, model, scenario, semantic ambiguity or
-- manufacturing tolerance are different obligations.  The axis stays typed;
-- heterogeneous claims are not silently scalarised.
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

TaggedAccept :
  ∀ {Candidate Axis ScenarioA ScenarioB : Set} →
  (Candidate → Axis → ScenarioA → Set) →
  (Candidate → Axis → ScenarioB → Set) →
  Candidate → Axis → ScenarioA ⊎ ScenarioB → Set
TaggedAccept acceptA acceptB candidate axis (inj₁ scenario) =
  acceptA candidate axis scenario
TaggedAccept acceptA acceptB candidate axis (inj₂ scenario) =
  acceptB candidate axis scenario

joinRobustScenarioFamilies :
  ∀ {Candidate Axis ScenarioA ScenarioB}
    {AcceptA : Candidate → Axis → ScenarioA → Set}
    {AcceptB : Candidate → Axis → ScenarioB → Set}
    {candidate : Candidate} {axis : Axis} →
  RobustAcross Candidate Axis ScenarioA AcceptA candidate axis →
  RobustAcross Candidate Axis ScenarioB AcceptB candidate axis →
  RobustAcross
    Candidate Axis (ScenarioA ⊎ ScenarioB)
    (TaggedAccept AcceptA AcceptB)
    candidate axis
joinRobustScenarioFamilies left right = record
  { DeclaredScenario = λ
      { (inj₁ scenario) → DeclaredScenario left scenario
      ; (inj₂ scenario) → DeclaredScenario right scenario
      }
  ; robust = λ
      { (inj₁ scenario) declaredHere → robust left scenario declaredHere
      ; (inj₂ scenario) declaredHere → robust right scenario declaredHere
      }
  }

------------------------------------------------------------------------
-- This composes declared scenario families only.  Robustness on one axis does
-- not imply robustness on another and no probability distribution is inferred.
------------------------------------------------------------------------
