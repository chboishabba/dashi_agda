module DASHI.Core.GovernedContactCore where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.DependencyPullbackCore as Pullback
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.ReplayArtifactCore as Replay

record GovernedContactCore : Set₁ where
  constructor governedContactCore
  field
    geometry     : Geometry.ObservableContactGeometry
    hamiltonian  : Hamiltonian.ContactHamiltonian
    replay       : Replay.ReplayArtifactCore
    gate         : Gate.ContactGateCore

    residualEncode :
      {left right : Geometry.Observable geometry} →
      Geometry.Residual geometry left right →
      Hamiltonian.Residual hamiltonian

    replayValidated       : Replay.replayable replay ≡ true
    replayDoesNotPromote  : Replay.replayPromotesTruth replay ≡ false
    gateFailClosed        : Gate.promotesTruth gate ≡ false

open GovernedContactCore public

scoreProjectedResidual :
  (core : GovernedContactCore) →
  {left right : Geometry.Observable (geometry core)} →
  Geometry.Residual (geometry core) left right →
  Hamiltonian.Energy (hamiltonian core)
scoreProjectedResidual core residual =
  Hamiltonian.Hamiltonian (hamiltonian core)
    (residualEncode core residual)

record ContactPromotionWitness (core : GovernedContactCore) : Set where
  constructor contactPromotionWitness
  field
    authorityClosed : Gate.authorityGateClosed (gate core) ≡ true
    bridgeClosed    : Gate.bridgeRequirementClosed (gate core) ≡ true
    replayLive      : Replay.replayable (replay core) ≡ true

open ContactPromotionWitness public

record PromotedContact (core : GovernedContactCore) : Set where
  constructor promotedContact
  field
    promotionWitness : ContactPromotionWitness core

open PromotedContact public

promotionRequiresClosedGate :
  (core : GovernedContactCore) →
  PromotedContact core →
  Gate.authorityGateClosed (gate core) ≡ true
promotionRequiresClosedGate core promoted =
  authorityClosed (promotionWitness promoted)

promotionRequiresClosedBridge :
  (core : GovernedContactCore) →
  PromotedContact core →
  Gate.bridgeRequirementClosed (gate core) ≡ true
promotionRequiresClosedBridge core promoted =
  bridgeClosed (promotionWitness promoted)

promotionRequiresLiveReplay :
  (core : GovernedContactCore) →
  PromotedContact core →
  Replay.replayable (replay core) ≡ true
promotionRequiresLiveReplay core promoted =
  replayLive (promotionWitness promoted)

record ContactDependencyNode : Set where
  constructor contactDependencyNode

contactReplayDependency :
  ContactDependencyNode → ContactDependencyNode →
  Pullback.DependencyEdge ContactDependencyNode
contactReplayDependency contact replay =
  Pullback.dependencyEdge contact replay

invalidReplayPullsBackContact :
  (contact replay : ContactDependencyNode) →
  Pullback.PullbackWitness ContactDependencyNode
invalidReplayPullsBackContact contact replay =
  Pullback.canonicalInvalidationPullback
    (contactReplayDependency contact replay)
