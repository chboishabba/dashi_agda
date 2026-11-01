module DASHI.Core.GovernedContactCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.DependencyPullbackCore as Pullback
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.ReplayArtifactCore as Replay

------------------------------------------------------------------------
-- Type-linked governed contact assembly.
--
-- The geometry and Hamiltonian remain reusable records, but this bundle makes
-- their compatibility explicit: every projected residual admitted by the
-- geometry must be encodable into the exact residual carrier scored by the
-- Hamiltonian.  Replay and gate layers are assembled beside that typed bridge.
------------------------------------------------------------------------

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

    replayValidated : Replay.replayable replay ≡ true
    replayDoesNotPromote : Replay.replayPromotesTruth replay ≡ false
    gateFailClosed : Gate.promotesTruth gate ≡ false

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

-- A promoted contact cannot be constructed from a status Bool alone.  It must
-- carry the closed authority, bridge, and replay witnesses.
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
