module DASHI.Governance.BoloBoloExternalChannelDominationNonDescentExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.RelationPolicyTransportComposition as RelationTransport

------------------------------------------------------------------------
-- EXTERNAL CHANNEL EVIDENCE != DOMINATION
--
-- The companion external-autonomy owner shows that internal governance alone
-- can miss external dependency.  This owner closes the reverse error: seeing
-- the same information-platform, financing/ownership, or relationship-network
-- channels does not determine who actually has decision authority, what is
-- contestable, or whether the target institution is dominated.
--
-- The fixtures are synthetic information-loss witnesses only.
------------------------------------------------------------------------

record ExternalChannelWorld : Set where
  constructor external-channel-world
  field
    informationPlatformPresentCode : Nat
    financingChannelPresentCode : Nat
    ownershipExposurePresentCode : Nat
    relationshipPathPresentCode : Nat

    externalDecisionAuthorityCode : Nat
    externalVetoOrConstraintCode : Nat
    subjectContestabilityCode : Nat

open ExternalChannelWorld public

ChannelPresenceOutcome : Set
ChannelPresenceOutcome = Nat × (Nat × (Nat × Nat))

ExternalAuthorityOutcome : Set
ExternalAuthorityOutcome = Nat × (Nat × Nat)

channelPresenceObserver : ExternalChannelWorld → ChannelPresenceOutcome
channelPresenceObserver world =
  informationPlatformPresentCode world ,
  (financingChannelPresentCode world ,
   (ownershipExposurePresentCode world , relationshipPathPresentCode world))

externalAuthorityConsumer : ExternalChannelWorld → ExternalAuthorityOutcome
externalAuthorityConsumer world =
  externalDecisionAuthorityCode world ,
  (externalVetoOrConstraintCode world , subjectContestabilityCode world)

------------------------------------------------------------------------
-- Same visible channels; different same-object authority/contestability.
------------------------------------------------------------------------

sameChannelsNoExternalAuthority : ExternalChannelWorld
sameChannelsNoExternalAuthority =
  external-channel-world 1 1 1 1 0 0 2

sameChannelsHighExternalAuthority : ExternalChannelWorld
sameChannelsHighExternalAuthority =
  external-channel-world 1 1 1 1 2 2 0

sameChannelPresenceCollision :
  channelPresenceObserver sameChannelsNoExternalAuthority ≡
  channelPresenceObserver sameChannelsHighExternalAuthority
sameChannelPresenceCollision = refl

externalAuthorityDiffers :
  externalAuthorityConsumer sameChannelsNoExternalAuthority ≡
  externalAuthorityConsumer sameChannelsHighExternalAuthority → ⊥
externalAuthorityDiffers ()

channelPresenceAuthorityNonDescent :
  Descent.ConsumerNonDescentWitness channelPresenceObserver externalAuthorityConsumer
channelPresenceAuthorityNonDescent =
  Descent.consumerNonDescentWitness
    sameChannelsNoExternalAuthority
    sameChannelsHighExternalAuthority
    sameChannelPresenceCollision
    externalAuthorityDiffers

channelPresenceCannotCertifyExternalAuthority :
  Descent.ConsumerSufficient channelPresenceObserver externalAuthorityConsumer → ⊥
channelPresenceCannotCertifyExternalAuthority =
  Descent.nonDescentWitnessBlocksSufficiency channelPresenceAuthorityNonDescent

externalAuthorityConsumerIsLeast :
  Descent.LeastSufficientConsumerObserver externalAuthorityConsumer
externalAuthorityConsumerIsLeast =
  Descent.canonicalConsumerObserverIsLeast externalAuthorityConsumer

everyAuthorityAdequateObserverRefinesCanonical :
  ∀ {Surface : Set}
    (observe : ExternalChannelWorld → Surface) →
  Descent.ConsumerSufficient observe externalAuthorityConsumer →
  Observer.Refines externalAuthorityConsumer observe
everyAuthorityAdequateObserverRefinesCanonical observe sufficient =
  Descent.belowEverySufficient externalAuthorityConsumerIsLeast observe sufficient

------------------------------------------------------------------------
-- Re-export the generic network-provenance firewall at the conceptual seam.
-- We deliberately do not manufacture a particular Epstein/Thiel/Palantir/
-- BlackRock/Blackstone path here.  Any application must instantiate the generic
-- relation system and proposition-specific transport licence on its own source.
------------------------------------------------------------------------

relationPathTransportOwnerPresent : Bool
relationPathTransportOwnerPresent = true

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ExternalChannelDominationBoundary : Set where
  constructor external-channel-domination-boundary
  field
    channelPresenceObserverConsumerSufficient : Bool
    externalAuthorityConsumerLeastSufficientPaid : Bool
    sameObservedChannelsCanHideDifferentDecisionAuthority : Bool
    sameObjectDecisionAuthorityAuditRequired : Bool
    sameObjectContestabilityAuditRequired : Bool

    relationPathAutoPromotesInfluence : Bool
    relationPathAutoPromotesKnowledge : Bool
    relationPathAutoPromotesCulpability : Bool
    financingChannelAutoPromotesControl : Bool
    platformCapabilityAutoPromotesAuthority : Bool
    ownershipExposureAutoPromotesCommonController : Bool
    channelCombinationAutoPromotesUnifiedCommand : Bool
    syntheticCollisionCreatesEmpiricalDominationFinding : Bool

open ExternalChannelDominationBoundary public

canonicalExternalChannelDominationBoundary : ExternalChannelDominationBoundary
canonicalExternalChannelDominationBoundary =
  external-channel-domination-boundary
    false true true true true
    false false false false false false false false
