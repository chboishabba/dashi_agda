module DASHI.Core.SocioEcologicalFeedbackExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A socio-ecological plan can change the behaviour of the people and
-- institutions embedded in the system.  Static cost/constraint equality is
-- therefore not generally a sufficient dynamic state.  This module gives an
-- exact finite non-factorability witness and an explicit reactive transition.
--
-- REFERENCE / MOTIVATION
--
-- Elinor Ostrom,
-- "Governing the Commons: The Evolution of Institutions for Collective Action",
-- Cambridge University Press, 1990.
-- DOI: 10.1017/CBO9780511807763.
--
-- Ostrom motivates endogenous institutional/collective-action response.  The
-- exact finite countermodel below is a DASHI construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core


data ActorDisposition : Set where
  cooperate resist : ActorDisposition

data Intervention : Set where
  voluntaryBuffer : Intervention

data StaticPlanScore : Set where
  sameDeclaredCost : StaticPlanScore

data World : Set where
  cooperativeWorld resistantWorld : World

data Outcome : Set where
  implemented blocked : Outcome

actorOf : World → ActorDisposition
actorOf cooperativeWorld = cooperate
actorOf resistantWorld = resist

staticScore : World → StaticPlanScore
staticScore cooperativeWorld = sameDeclaredCost
staticScore resistantWorld = sameDeclaredCost

react : Intervention → World → Outcome
react voluntaryBuffer cooperativeWorld = implemented
react voluntaryBuffer resistantWorld = blocked

staticScoreCollision : staticScore cooperativeWorld ≡ staticScore resistantWorld
staticScoreCollision = refl

staticPlanScoreCannotDetermineReactiveOutcome :
  Core.ConsumerDescentDefect staticScore (react voluntaryBuffer)
staticPlanScoreCannotDetermineReactiveOutcome =
  Core.consumerDescentDefect cooperativeWorld resistantWorld refl impossible
  where
    impossible : implemented ≡ blocked → ⊥
    impossible ()

record ReactiveAgentSystem : Set₁ where
  constructor reactiveAgentSystem
  field
    AgentState : Set
    observeActor : World → AgentState
    respond : Intervention → AgentState → Outcome
    responseMatchesWorld :
      ∀ intervention world →
      respond intervention (observeActor world) ≡ react intervention world

open ReactiveAgentSystem public

canonicalReactiveAgentSystem : ReactiveAgentSystem
canonicalReactiveAgentSystem =
  reactiveAgentSystem ActorDisposition actorOf response proof
  where
    response : Intervention → ActorDisposition → Outcome
    response voluntaryBuffer cooperate = implemented
    response voluntaryBuffer resist = blocked

    proof :
      ∀ intervention world →
      response intervention (actorOf world) ≡ react intervention world
    proof voluntaryBuffer cooperativeWorld = refl
    proof voluntaryBuffer resistantWorld = refl

record SocioEcologicalFeedbackBoundary : Set where
  constructor socioEcologicalFeedbackBoundary
  field
    staticCostEqualityNeedNotDetermineImplementationOutcome : Bool
    humanResponseCanBePartOfSystemDynamics : Bool
    actorModelMustNotBeInferredFromCostAlone : Bool
    reactiveDynamicsDoNotByThemselvesSupplyLegitimateGovernance : Bool

canonicalSocioEcologicalFeedbackBoundary : SocioEcologicalFeedbackBoundary
canonicalSocioEcologicalFeedbackBoundary =
  socioEcologicalFeedbackBoundary true true true true
