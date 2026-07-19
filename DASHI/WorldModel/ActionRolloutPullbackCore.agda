module DASHI.WorldModel.ActionRolloutPullbackCore where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.DependencyPullbackCore as Pullback

------------------------------------------------------------------------
-- Pullback wiring for action-conditioned rollouts.
------------------------------------------------------------------------

data WorldModelNode : Set where
  rolloutNode    : WorldModelNode
  dependencyNode : WorldModelNode

record RolloutDependency : Set where
  constructor rolloutDependency
  field
    rollout    : WorldModelNode
    dependency : WorldModelNode

open RolloutDependency public

asDependencyEdge :
  RolloutDependency → Pullback.DependencyEdge WorldModelNode
asDependencyEdge relation =
  Pullback.dependencyEdge
    (rollout relation)
    (dependency relation)

record RolloutPullbackReceipt : Set where
  constructor rolloutPullbackReceipt
  field
    relation : RolloutDependency
    witness  : Pullback.PullbackWitness WorldModelNode

open RolloutPullbackReceipt public

canonicalRolloutPullback : RolloutDependency → RolloutPullbackReceipt
canonicalRolloutPullback relation =
  rolloutPullbackReceipt relation
    (Pullback.canonicalInvalidationPullback (asDependencyEdge relation))

invalidDependencyPullsBackRollout :
  (relation : RolloutDependency) →
  Pullback.downstreamAfter (witness (canonicalRolloutPullback relation))
    ≡ Pullback.pulledBack
invalidDependencyPullsBackRollout relation =
  Pullback.pulledBackBlocksPromotion
    (witness (canonicalRolloutPullback relation))
    refl
