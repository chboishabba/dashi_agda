module DASHI.Biology.DrosophilaConsumerIndexedEvidencePromotionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Dep

------------------------------------------------------------------------
-- Evidence sufficiency is consumer-relative.  A receipt that is adequate for
-- structure->function benchmarking need not authorize effector, behavioural, or
-- semantic promotion.
------------------------------------------------------------------------

data EvidenceConsumer : Set where
  structuralFunctionalConsumer : EvidenceConsumer
  neuralStateConsumer : EvidenceConsumer
  effectorStateConsumer : EvidenceConsumer
  behaviourConsumer : EvidenceConsumer
  semanticConsumer : EvidenceConsumer

data EvidenceChannel : Set where
  connectomeChannel : EvidenceChannel
  calciumChannel : EvidenceChannel
  voltageChannel : EvidenceChannel
  ephysChannel : EvidenceChannel
  registrationChannel : EvidenceChannel
  muscleActivationChannel : EvidenceChannel
  kinematicsChannel : EvidenceChannel
  contactForceChannel : EvidenceChannel
  environmentChannel : EvidenceChannel
  interactionChannel : EvidenceChannel

data ConsumerBoundary : Set where
  noNeuralPromotionImpliesEffectorPromotion : ConsumerBoundary
  noEffectorPromotionImpliesBehaviourMeaning : ConsumerBoundary
  noBehaviourMotifImpliesSemanticPromotion : ConsumerBoundary
  noConsumerReceiptsSilentlyTransfer : ConsumerBoundary
  noDependentChannelsCountAsIndependentReplicates : ConsumerBoundary

record ConsumerEvidencePolicy : Set₁ where
  field
    required : EvidenceConsumer → List EvidenceChannel
    optional : EvidenceConsumer → List EvidenceChannel
    independenceRequired : EvidenceConsumer → Bool
    policyReading : EvidenceConsumer → String

open ConsumerEvidencePolicy public

record ConsumerEvidenceBundle : Set₁ where
  field
    ChannelArtifact : Set
    consumer : EvidenceConsumer
    channels : List EvidenceChannel
    artifacts : List ChannelArtifact
    dependenceRelation : Dep.EvidenceRelation
    allRequiredPresent : Bool
    allRequiredPresentIsTrue : allRequiredPresent ≡ true
    provenanceAdequate : Bool
    provenanceAdequateIsTrue : provenanceAdequate ≡ true

open ConsumerEvidenceBundle public

record ConsumerPromotionReceipt : Set₁ where
  field
    bundle : ConsumerEvidenceBundle
    receiptID : String
    promotedForConsumer : EvidenceConsumer
    promotionAdmissible : Bool
    promotionAdmissibleIsTrue : promotionAdmissible ≡ true

open ConsumerPromotionReceipt public

record CrossConsumerTransfer : Set where
  field
    sourceConsumer : EvidenceConsumer
    targetConsumer : EvidenceConsumer
    transferReceipt : String
    transferAdmissible : Bool

open CrossConsumerTransfer public

canonicalConsumerBoundaries : List ConsumerBoundary
canonicalConsumerBoundaries =
  noNeuralPromotionImpliesEffectorPromotion
  ∷ noEffectorPromotionImpliesBehaviourMeaning
  ∷ noBehaviourMotifImpliesSemanticPromotion
  ∷ noConsumerReceiptsSilentlyTransfer
  ∷ noDependentChannelsCountAsIndependentReplicates
  ∷ []
