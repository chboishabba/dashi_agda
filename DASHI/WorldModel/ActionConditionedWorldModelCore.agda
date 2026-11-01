module DASHI.WorldModel.ActionConditionedWorldModelCore where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.DependencyPullbackCore as Pullback

------------------------------------------------------------------------
-- Action-conditioned world-model surface.
--
-- The primitive is not State -> Future.  A rollout is conditioned on a
-- candidate action sequence, then scored by task and guard objectives.  Action
-- selection is proof-bearing: the dependency must be live and the authority /
-- bridge gate must be closed before a selected sequence can be promoted.
------------------------------------------------------------------------

record ActionConditionedWorldModelCore : Set₁ where
  constructor actionConditionedWorldModelCore
  field
    State       : Set
    Action      : Set
    Trajectory  : Set
    TaskEnergy  : Set
    GuardEnergy : Set
    Dependency  : Set

    rollout     : State → List Action → Trajectory
    taskEnergy  : Trajectory → TaskEnergy
    guardEnergy : Trajectory → GuardEnergy

    dependencyStatus : Dependency → Pullback.DependencyStatus
    actionGate       : List Action → Gate.ContactGateCore

open ActionConditionedWorldModelCore public

record ActionPromotionWitness
  (model : ActionConditionedWorldModelCore)
  (dependency : Dependency model)
  (actions : List (Action model)) : Set where
  constructor actionPromotionWitness
  field
    dependencyLive : dependencyStatus model dependency ≡ Pullback.live
    authorityClosed :
      Gate.authorityGateClosed (actionGate model actions) ≡ true
    bridgeClosed :
      Gate.bridgeRequirementClosed (actionGate model actions) ≡ true

open ActionPromotionWitness public

record SelectedActionSequence
  (model : ActionConditionedWorldModelCore)
  (dependency : Dependency model) : Set where
  constructor selectedActionSequence
  field
    actions          : List (Action model)
    promotionWitness : ActionPromotionWitness model dependency actions

open SelectedActionSequence public

selectedActionDependenciesLive :
  (model : ActionConditionedWorldModelCore) →
  (dependency : Dependency model) →
  (selected : SelectedActionSequence model dependency) →
  dependencyStatus model dependency ≡ Pullback.live
selectedActionDependenciesLive model dependency selected =
  dependencyLive (promotionWitness selected)

selectedActionAuthorityClosed :
  (model : ActionConditionedWorldModelCore) →
  (dependency : Dependency model) →
  (selected : SelectedActionSequence model dependency) →
  Gate.authorityGateClosed
    (actionGate model (actions selected)) ≡ true
selectedActionAuthorityClosed model dependency selected =
  authorityClosed (promotionWitness selected)

predictedTrajectory :
  (model : ActionConditionedWorldModelCore) →
  State model →
  {dependency : Dependency model} →
  SelectedActionSequence model dependency →
  Trajectory model
predictedTrajectory model state selected =
  rollout model state (actions selected)
