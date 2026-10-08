module DASHI.Biology.DyadicSynchronyDevelopmentalAttunementBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.GABAPhenotypeEvidenceInstantiationExact as GABA
import DASHI.Biology.AliceBrownThreadInquirySynthesisExact as Alice
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Attunement

------------------------------------------------------------------------
-- DYADIC SYNCHRONY / DEVELOPMENTAL ATTUNEMENT WELD
--
-- Existing DevelopmentalAttunementPNFBridge already owns the typed parent-child
-- / caregiver-dependent dyad and proves that equal response quantity can have
-- different fragmentation burden because response order matters.  The Nguyen
-- synchrony/attachment receipt is therefore attached to this existing owner,
-- not used to create a new scalar "dyadic synchrony" ontology.
------------------------------------------------------------------------

record DyadicSynchronyAttunementBridge : Set where
  constructor dyadic-synchrony-attunement-bridge
  field
    synchronyAssociation : GABA.SynchronyAttachmentAssociationReceipt
    relationKind : Attunement.DevelopmentalRelation
    fragmentationWitness :
      Attunement.SameQuantityGreaterFragmentation
        Attunement.stableTrace
        Attunement.fragmentedTrace
    aliceSynthesis : Alice.AliceBrownThreadInquirySynthesis
    synchronyIsInteractionMeasurement : Bool
    synchronyIsInteractionMeasurementIsTrue :
      synchronyIsInteractionMeasurement ≡ true
    synchronyDeterminesResponseSequence : Bool
    synchronyDeterminesResponseSequenceIsFalse :
      synchronyDeterminesResponseSequence ≡ false
    synchronyDeterminesAttachment : Bool
    synchronyDeterminesAttachmentIsFalse : synchronyDeterminesAttachment ≡ false
    synchronyCollapsesCaregiverAndChildObservers : Bool
    synchronyCollapsesCaregiverAndChildObserversIsFalse :
      synchronyCollapsesCaregiverAndChildObservers ≡ false
    bridgeReference : String

open DyadicSynchronyAttunementBridge public

canonicalDyadicSynchronyAttunementBridge : DyadicSynchronyAttunementBridge
canonicalDyadicSynchronyAttunementBridge =
  dyadic-synchrony-attunement-bridge
    GABA.nguyen2024SynchronyAttachmentAssociation
    Attunement.parentChildRelation
    Attunement.canonicalFragmentationWitness
    Alice.canonicalAliceBrownThreadInquirySynthesis
    true refl false refl false refl false refl
    "Nguyen's fNIRS synchrony association is placed on the existing parent-child developmental-relation owner. Attunement response ordering/fragmentation and caregiver/child situated evidence remain separate coordinates; neural synchrony does not recover the ordered response trace or define attachment."

data SynchronyRecoversOrderedResponseTracePermission : Set where
data SynchronyCollapsesDyadObserversPermission : Set where

synchronyDoesNotRecoverOrderedResponseTrace :
  SynchronyRecoversOrderedResponseTracePermission → Alice.Never
synchronyDoesNotRecoverOrderedResponseTrace ()

synchronyDoesNotCollapseDyadObservers :
  SynchronyCollapsesDyadObserversPermission → Alice.Never
synchronyDoesNotCollapseDyadObservers ()

record DyadicSynchronyAttunementBoundary : Set where
  constructor dyadic-synchrony-attunement-boundary
  field
    existingDyadOwnerReused : Bool
    existingDyadOwnerReusedIsTrue : existingDyadOwnerReused ≡ true
    existingFragmentationTheoremReused : Bool
    existingFragmentationTheoremReusedIsTrue :
      existingFragmentationTheoremReused ≡ true
    synchronyAssociationAttachedWithoutDefinition : Bool
    synchronyAssociationAttachedWithoutDefinitionIsTrue :
      synchronyAssociationAttachedWithoutDefinition ≡ true
    orderedInteractionTraceRemainsLatentToSynchronyMeasurement : Bool
    orderedInteractionTraceRemainsLatentToSynchronyMeasurementIsTrue :
      orderedInteractionTraceRemainsLatentToSynchronyMeasurement ≡ true
    observerPluralityRetained : Bool
    observerPluralityRetainedIsTrue : observerPluralityRetained ≡ true

canonicalDyadicSynchronyAttunementBoundary : DyadicSynchronyAttunementBoundary
canonicalDyadicSynchronyAttunementBoundary =
  dyadic-synchrony-attunement-boundary true refl true refl true refl true refl true refl
