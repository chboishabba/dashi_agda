module DASHI.Biology.DyadicSynchronyDevelopmentalAttunementBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
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

gordonBartsch2026Source : Source.AttributedSource
gordonBartsch2026Source =
  Source.mkDOISource
    "Ilanit Gordon; Ronny P. Bartsch"
    "Correlates of interpersonal physiological synchrony and sources of empirical heterogeneity"
    "Nature Reviews Psychology 5:201-215"
    "2026"
    "10.1038/s44159-026-00535-4"
    "https://doi.org/10.1038/s44159-026-00535-4"
    Source.academicArticleSource
    "Review-level synthesis of interpersonal physiological synchrony findings. It explicitly characterizes the psychological meaning of physiological synchrony as ambiguous and separates social-, performance- and self-oriented correlates while emphasizing methodological and theoretical heterogeneity. It does not license attachment classification from synchrony alone."
    Source.publicAttribution

record DyadicSynchronyAttunementBridge : Set where
  constructor dyadic-synchrony-attunement-bridge
  field
    synchronyAssociation : GABA.SynchronyAttachmentAssociationReceipt
    heterogeneityReview : Source.AttributedSource
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
    synchronyMeaningIsUniquePsychologicalClassifier : Bool
    synchronyMeaningIsUniquePsychologicalClassifierIsFalse :
      synchronyMeaningIsUniquePsychologicalClassifier ≡ false
    synchronyCollapsesCaregiverAndChildObservers : Bool
    synchronyCollapsesCaregiverAndChildObserversIsFalse :
      synchronyCollapsesCaregiverAndChildObservers ≡ false
    bridgeReference : String

open DyadicSynchronyAttunementBridge public

canonicalDyadicSynchronyAttunementBridge : DyadicSynchronyAttunementBridge
canonicalDyadicSynchronyAttunementBridge =
  dyadic-synchrony-attunement-bridge
    GABA.nguyen2024SynchronyAttachmentAssociation
    gordonBartsch2026Source
    Attunement.parentChildRelation
    Attunement.canonicalFragmentationWitness
    Alice.canonicalAliceBrownThreadInquirySynthesis
    true refl false refl false refl false refl false refl
    "Nguyen's fNIRS synchrony association is placed on the existing parent-child developmental-relation owner and bounded by Gordon/Bartsch 2026's review-level heterogeneity result. Attunement response ordering/fragmentation and caregiver/child situated evidence remain separate coordinates; neural or physiological synchrony does not recover the ordered response trace, define attachment, or carry one unique psychological meaning."

data SynchronyRecoversOrderedResponseTracePermission : Set where
data SynchronyCollapsesDyadObserversPermission : Set where
data SynchronyDefinesUniquePsychologicalStatePermission : Set where

synchronyDoesNotRecoverOrderedResponseTrace :
  SynchronyRecoversOrderedResponseTracePermission → Alice.Never
synchronyDoesNotRecoverOrderedResponseTrace ()

synchronyDoesNotCollapseDyadObservers :
  SynchronyCollapsesDyadObserversPermission → Alice.Never
synchronyDoesNotCollapseDyadObservers ()

synchronyDoesNotDefineUniquePsychologicalState :
  SynchronyDefinesUniquePsychologicalStatePermission → Alice.Never
synchronyDoesNotDefineUniquePsychologicalState ()

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
    heterogeneityReviewRetained : Bool
    heterogeneityReviewRetainedIsTrue : heterogeneityReviewRetained ≡ true
    synchronyMeaningIsUniquePsychologicalClassifier : Bool
    synchronyMeaningIsUniquePsychologicalClassifierIsFalse :
      synchronyMeaningIsUniquePsychologicalClassifier ≡ false
    orderedInteractionTraceRemainsLatentToSynchronyMeasurement : Bool
    orderedInteractionTraceRemainsLatentToSynchronyMeasurementIsTrue :
      orderedInteractionTraceRemainsLatentToSynchronyMeasurement ≡ true
    observerPluralityRetained : Bool
    observerPluralityRetainedIsTrue : observerPluralityRetained ≡ true

open DyadicSynchronyAttunementBoundary public

canonicalDyadicSynchronyAttunementBoundary : DyadicSynchronyAttunementBoundary
canonicalDyadicSynchronyAttunementBoundary =
  dyadic-synchrony-attunement-boundary
    true refl true refl true refl true refl false refl true refl true refl
