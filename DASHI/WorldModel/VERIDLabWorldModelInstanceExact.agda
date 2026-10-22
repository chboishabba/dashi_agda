module DASHI.WorldModel.VERIDLabWorldModelInstanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Data.Empty using (⊥)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.DependencyPullbackCore as Pullback
import DASHI.WorldModel.ActionConditionedWorldModelCore as World
import DASHI.WorldModel.PredicateNormalWorldModelCore as PNW
import DASHI.WorldModel.ActionRolloutPullbackCore as Rollback
import DASHI.Core.ConsumerFibreRepairExact as Repair

------------------------------------------------------------------------
-- Bounded integration of VERID-style laboratory execution with the
-- canonical DASHI world model. Not a second transition semantics.
--
-- Simulation/closed governance gates are not hardware validation. The
-- explicit LabExecutionContact record below names that remaining payment.
------------------------------------------------------------------------

record LabWorldModelInstance : Set₁ where
  constructor labWorldModelInstance
  field
    world : World.ActionConditionedWorldModelCore
    physicalSafe :
      World.State world → List (World.Action world) → Set
    modelConforms :
      World.State world → List (World.Action world) → Set
    observationReconciled :
      World.State world → List (World.Action world) → Set

open LabWorldModelInstance public

record LabExecutionContact
  (lab : LabWorldModelInstance)
  (s : World.State (world lab))
  (dependency : World.Dependency (world lab)) : Set where
  constructor labExecutionContact
  field
    selected : World.SelectedActionSequence (world lab) dependency
    safetyPayment : physicalSafe lab s (World.actions selected)
    conformityPayment : modelConforms lab s (World.actions selected)
    observationPayment :
      observationReconciled lab s (World.actions selected)

open LabExecutionContact public

contactHasLiveDependency :
  (lab : LabWorldModelInstance) →
  (s : World.State (world lab)) →
  (dependency : World.Dependency (world lab)) →
  (contact : LabExecutionContact lab s dependency) →
  World.dependencyStatus (world lab) dependency ≡ Pullback.live
contactHasLiveDependency lab s dependency contact =
  World.selectedActionDependenciesLive
    (world lab) dependency (selected contact)

contactHasClosedAuthority :
  (lab : LabWorldModelInstance) →
  (s : World.State (world lab)) →
  (dependency : World.Dependency (world lab)) →
  (contact : LabExecutionContact lab s dependency) →
  Gate.authorityGateClosed
    (World.actionGate (world lab) (World.actions (selected contact)))
      ≡ true
contactHasClosedAuthority lab s dependency contact =
  World.selectedActionAuthorityClosed
    (world lab) dependency (selected contact)

------------------------------------------------------------------------
-- A deliberately fail-closed finite laboratory fixture. The observer and
-- rollout are intentionally uninformative; NO execution can be certified.
-- This regression catches accidental promotion from simulation alone.
------------------------------------------------------------------------

fixtureWorld : World.ActionConditionedWorldModelCore
fixtureWorld = World.actionConditionedWorldModelCore
  Bool Bool Bool Bool Bool Bool
  (λ _ _ → false)
  (λ _ → false)
  (λ _ → false)
  (λ _ → Pullback.live)
  (λ _ → Gate.canonicalFailClosedContactGate)

fixtureLab : LabWorldModelInstance
fixtureLab = labWorldModelInstance
  fixtureWorld
  (λ _ _ → ⊥)
  (λ _ _ → ⊥)
  (λ _ _ → ⊥)

fixtureCannotPromote :
  (dependency : World.Dependency fixtureWorld) →
  (actions : List (World.Action fixtureWorld)) →
  World.ActionPromotionWitness fixtureWorld dependency actions → ⊥
fixtureCannotPromote dependency actions witness
  with World.authorityClosed witness
... | ()

fixtureCannotDispatch :
  (state : World.State fixtureWorld) →
  (dependency : World.Dependency fixtureWorld) →
  LabExecutionContact fixtureLab state dependency → ⊥
fixtureCannotDispatch state dependency contact =
  fixtureCannotPromote dependency
    (World.actions (selected contact))
    (World.promotionWitness (selected contact))

------------------------------------------------------------------------
-- Integration anchors: reuse existing PNF proposal boundaries, dependency
-- rollback, and consumer-relative observer repair without redefining them.
------------------------------------------------------------------------

proposalDoesNotPromote :
  (model : PNW.PredicateNormalWorldModelCore) →
  (observation : PNW.Observation model) →
  PNW.PredicateNormalProposalBoundary model observation →
  Gate.promotesTruth
    (PNW.actionGate model (PNW.candidateActions model observation)) ≡ false
proposalDoesNotPromote model observation boundary =
  PNW.candidateGateDoesNotAutoPromote boundary

invalidatedRolloutIsPulledBack :
  (relation : Rollback.RolloutDependency) →
  Pullback.downstreamAfter
    (Rollback.witness (Rollback.canonicalRolloutPullback relation))
      ≡ Pullback.pulledBack
invalidatedRolloutIsPulledBack =
  Rollback.invalidDependencyPullsBackRollout
