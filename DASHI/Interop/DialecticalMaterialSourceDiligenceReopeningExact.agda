module DASHI.Interop.DialecticalMaterialSourceDiligenceReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.DialecticalMaterialRevisionExact as Material
import DASHI.Core.DialecticalMaterialFutureSafetyExact as Future
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as Diligence
import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- DIALECTICAL / MATERIAL REOPENING -> EPISTEMIC LINEAGE -> PRODUCER
--
-- A changed material condition, activated tension, or future-safety defect is a
-- reason to recompute a consumer-relative claim.  It is not itself a source
-- defect, refutation, or search authority.  Reopening becomes executable only
-- after an explicit first-missing source/provenance coordinate is identified.
------------------------------------------------------------------------

data ReopeningTrigger : Set where
  materialConditionChanged
  tensionActivated
  futureConsumerCollision
  interpretationReframed
  : ReopeningTrigger

record DialecticalSourceReopening : Set where
  constructor dialectical-source-reopening
  field
    claimReference : String
    trigger : ReopeningTrigger
    sourceKind : Shape.SourceBearingObjectKind
    requiredShape : Shape.RequiredAttributionShape
    requiredShapeMatchesCarrier :
      requiredShape ≡ Shape.requiredAttributionShape sourceKind
    firstMissingSourceCoordinate : Diligence.SourceDiligenceGap
    requiredProducer : Search.ProducerClass
    requiredProducerMatchesGap :
      requiredProducer ≡
      Diligence.producerForSourceDiligenceGap firstMissingSourceCoordinate
    priorEvidenceRetained : Bool
    currentConclusionMustBeRecomputed : Bool
    consumerReference : String
    reopeningReference : String

open DialecticalSourceReopening public

reopeningDemand :
  (claimRef : String) →
  (trigger : ReopeningTrigger) →
  (kind : Shape.SourceBearingObjectKind) →
  (gap : Diligence.SourceDiligenceGap) →
  (consumerRef : String) →
  (reopeningRef : String) →
  DialecticalSourceReopening
reopeningDemand claimRef trigger kind gap consumerRef reopeningRef =
  dialectical-source-reopening
    claimRef
    trigger
    kind
    (Shape.requiredAttributionShape kind)
    refl
    gap
    (Diligence.producerForSourceDiligenceGap gap)
    refl
    true
    true
    consumerRef
    reopeningRef

------------------------------------------------------------------------
-- Exact examples: same structural trigger, different epistemic lineage gaps,
-- therefore different highest-alpha producers.
------------------------------------------------------------------------

empiricalMaterialShiftNeedsCoverage : DialecticalSourceReopening
empiricalMaterialShiftNeedsCoverage =
  reopeningDemand
    "materially-sensitive empirical claim"
    materialConditionChanged
    Shape.publishedEmpiricalClaim
    Diligence.coverageUnresolved
    "future material-state consumer"
    "Changed conditions expose unresolved empirical coverage; acquire the missing evidence panel."

interpretiveTensionNeedsBoundary : DialecticalSourceReopening
interpretiveTensionNeedsBoundary =
  reopeningDemand
    "historical / interpretive claim"
    tensionActivated
    Shape.interpretiveOrCulturalSource
    Diligence.interpretationBoundaryOpen
    "historical interpretation consumer"
    "Activated tension reopens the interpretation boundary without refuting the retained source text."

communityUseNeedsAuthority : DialecticalSourceReopening
communityUseNeedsAuthority =
  reopeningDemand
    "community-knowledge use claim"
    futureConsumerCollision
    Shape.communityKnowledgeOrAuthority
    Diligence.authorityOpen
    "authority-sensitive action consumer"
    "Future-use collision requires authority/mandate evidence, not another generic citation."

archiveIdentityNeedsSameObject : DialecticalSourceReopening
archiveIdentityNeedsSameObject =
  reopeningDemand
    "local archive / executable source claim"
    interpretationReframed
    Shape.localArchiveOrCodeContract
    Diligence.sameObjectUnresolved
    "same-carrier reconstruction consumer"
    "Reframing exposes a same-object weld gap; preserve hash/path/revision provenance."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DialecticalContradictionIsSourceRefutation : Set where
data MaterialChangeSelectsProducerWithoutGap : Set where
data ReopeningDeletesPriorEvidence : Set where
data GenericCitationRepairsEveryCarrier : Set where
data ProducerSelectionCreatesActionAuthority : Set where

dialecticalContradictionDoesNotRefuteSourceByItself :
  DialecticalContradictionIsSourceRefutation → ⊥
dialecticalContradictionDoesNotRefuteSourceByItself ()

materialChangeDoesNotSelectProducerWithoutTypedGap :
  MaterialChangeSelectsProducerWithoutGap → ⊥
materialChangeDoesNotSelectProducerWithoutGap ()

reopeningNeedNotDeletePriorEvidence : ReopeningDeletesPriorEvidence → ⊥
reopeningNeedNotDeletePriorEvidence ()

genericCitationDoesNotRepairEveryCarrier : GenericCitationRepairsEveryCarrier → ⊥
genericCitationDoesNotRepairEveryCarrier ()

producerSelectionDoesNotCreateActionAuthority :
  ProducerSelectionCreatesActionAuthority → ⊥
producerSelectionDoesNotCreateActionAuthority ()

------------------------------------------------------------------------
-- Existing donor boundaries are carried explicitly rather than restated.
------------------------------------------------------------------------

materialRevisionBoundary : Material.DialecticalMaterialRevisionBoundary
materialRevisionBoundary = Material.canonicalDialecticalMaterialRevisionBoundary

futureSafetyBoundary : Future.DialecticalMaterialFutureSafetyBoundary
futureSafetyBoundary = Future.canonicalDialecticalMaterialFutureSafetyBoundary

sourceShapeBoundary : Shape.SourceAttributionShapeBoundary
sourceShapeBoundary = Shape.canonicalSourceAttributionShapeBoundary

sourceSearchBoundary : Diligence.SourceDiligenceProofSearchBoundary
sourceSearchBoundary = Diligence.canonicalSourceDiligenceProofSearchBoundary

record DialecticalMaterialSourceReopeningBoundary : Set where
  constructor dialectical-material-source-reopening-boundary
  field
    materialChangeMayReopenClaim : Bool
    reopeningRequiresTypedEpistemicGap : Bool
    sourceShapeDependsOnCarrier : Bool
    priorEvidenceMayRemainRetained : Bool
    contradictionAloneIsRefutation : Bool
    producerChoiceEqualsActionAuthority : Bool

canonicalDialecticalMaterialSourceReopeningBoundary :
  DialecticalMaterialSourceReopeningBoundary
canonicalDialecticalMaterialSourceReopeningBoundary =
  dialectical-material-source-reopening-boundary
    true true true true false false
