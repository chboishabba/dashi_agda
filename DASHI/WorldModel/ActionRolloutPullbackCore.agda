module DASHI.WorldModel.ActionRolloutPullbackCore where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.DependencyPullbackCore as Pullback

------------------------------------------------------------------------
-- Pullback wiring for action-conditioned rollouts.
--
-- When a mechanism, source, calibration, or replay dependency is invalidated,
-- every downstream rollout that imports it moves to pulledBack.  This is a
-- status theorem only; it does not claim that the world mechanism is recovered.
------------------------------------------------------------------------

record RolloutNode : Set where
  constructor rolloutNode

record DependencyNode : Set where
  constructor dependencyNode

record RolloutDependency : Set where
  constructor rolloutDependency
  field
    rollout    : RolloutNode
    dependency : DependencyNode

open RolloutDependency public

asDependencyEdge : RolloutDependency → Pullback.DependencyEdge RolloutNode
asDependencyEdge relation =
  Pullback.dependencyEdge (rollout relation) (rollout relation)

record RolloutPullbackReceipt : Set where
  constructor rolloutPullbackReceipt
  field
    relation : RolloutDependency
    witness  : Pullback.PullbackWitness RolloutNode

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
    Agda.Builtin.Equality.refl
