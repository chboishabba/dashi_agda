module DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as Canonical
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Consumer
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as FutureCanonical

------------------------------------------------------------------------
-- TYPED HYPERFABRIC GLOBAL-SECTION -> CONSUMER-RELATIVE REDUCTION BRIDGE
--
-- No new fibre/sheaf/reduction kernel is introduced here. A compatible
-- Hyperfabric.GlobalSection is simply used as the Fine state of the already
-- canonical ConsumerRelativeReduction kernel. The reduced state is therefore
-- explicitly a consumer-facing quotient/projection of compatible sections,
-- not a claim that the physical/local fabric itself has collapsed.
------------------------------------------------------------------------

HyperfabricSectionReduction :
  {Vertex Edge : Set} →
  Hyperfabric.TypedHyperfabric Vertex Edge →
  Set → Set → Set₁
HyperfabricSectionReduction fabric Action Observation =
  Reduction.ConsumerRelativeReduction
    (Hyperfabric.GlobalSection fabric)
    Action
    Observation

sectionCurrentConsumerDescent :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (rom : HyperfabricSectionReduction fabric Action Observation) →
  Consumer.ConsumerDescent
    (Reduction.encode rom)
    (Reduction.fineObserve rom)
sectionCurrentConsumerDescent = Canonical.currentConsumerDescent

sectionActionIntertwiner :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (rom : HyperfabricSectionReduction fabric Action Observation) →
  (action : Action) →
  Consumer.Intertwiner
    (Reduction.encode rom)
    (Reduction.encode rom)
    (Reduction.fineStep rom action)
    (Reduction.reducedStep rom action)
sectionActionIntertwiner = Canonical.actionIntertwiner

sectionCanonicalFutureSafety :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (rom : HyperfabricSectionReduction fabric Action Observation) →
  (actionLabel : Action → String) →
  Future.FutureLanguageSafeProjection
    (FutureCanonical.deterministicSystem (Reduction.fineStep rom) actionLabel)
    (Reduction.fineObserve rom)
    (Reduction.encode rom)
sectionCanonicalFutureSafety = Canonical.canonicalFutureSafety

------------------------------------------------------------------------
-- Finite exact specimen.
--
-- One compatible global section carries a visible coordinate and an extra
-- hidden/local coordinate in its vertex stalk. The declared consumer sees
-- only the visible coordinate. Two globally compatible sections may then
-- collapse to the same consumer code while remaining distinct local-stalk
-- assignments. This is consumer quotienting of sections, not stalk identity.
------------------------------------------------------------------------

data SpecVertex : Set where
  region : SpecVertex

data SpecEdge : Set where
  relation : SpecEdge

data SpecIncidence : SpecVertex → SpecEdge → Set where
  regionOnRelation : SpecIncidence region relation

specFabric : Hyperfabric.TypedHyperfabric SpecVertex SpecEdge
specFabric = record
  { vertexStalk = λ _ → Bool × Bool
  ; edgeStalk = λ _ → Bool
  ; incidence = SpecIncidence
  ; restrict = λ _ pair → proj₁ pair
  ; edgeProvenance = λ _ → "finite section-reduction specimen" ∷ []
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "finite hyperfabric section consumer-reduction specimen"
  }

leftSection : Hyperfabric.GlobalSection specFabric
leftSection = record
  { vertexValue = λ _ → false , false
  ; edgeValue = λ _ → false
  ; compatible = λ _ → refl
  ; sectionReceipt = "visible=false; hidden=false"
  }

rightSection : Hyperfabric.GlobalSection specFabric
rightSection = record
  { vertexValue = λ _ → false , true
  ; edgeValue = λ _ → false
  ; compatible = λ _ → refl
  ; sectionReceipt = "visible=false; hidden=true"
  }

sectionVisible : Hyperfabric.GlobalSection specFabric → Bool
sectionVisible section = proj₁ (Hyperfabric.vertexValue section region)

specReduction : HyperfabricSectionReduction specFabric ⊤ Bool
specReduction = Reduction.consumerRelativeReduction
  Bool
  sectionVisible
  (λ _ section → section)
  (λ _ code → code)
  sectionVisible
  (λ code → code)
  (λ _ _ → refl)
  (λ _ → refl)

hiddenStalkDifferenceCanCollapseForDeclaredConsumer :
  Reduction.encode specReduction leftSection
  ≡ Reduction.encode specReduction rightSection
hiddenStalkDifferenceCanCollapseForDeclaredConsumer = refl

finiteSectionConsumerDescent :
  Consumer.ConsumerDescent
    (Reduction.encode specReduction)
    (Reduction.fineObserve specReduction)
finiteSectionConsumerDescent = sectionCurrentConsumerDescent specReduction

finiteSectionFutureSafe :
  Future.FutureLanguageSafeProjection
    (FutureCanonical.deterministicSystem
      (Reduction.fineStep specReduction)
      (λ _ → "identity section action"))
    (Reduction.fineObserve specReduction)
    (Reduction.encode specReduction)
finiteSectionFutureSafe =
  sectionCanonicalFutureSafety specReduction (λ _ → "identity section action")

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record HyperfabricConsumerReductionBoundary : Set where
  constructor hyperfabric-consumer-reduction-boundary
  field
    globalSectionMayServeAsFineReductionState : Bool
    globalSectionMayServeAsFineReductionStateIsTrue :
      globalSectionMayServeAsFineReductionState ≡ true

    reductionActsOnCompatibleSectionsNotBareStalks : Bool
    reductionActsOnCompatibleSectionsNotBareStalksIsTrue :
      reductionActsOnCompatibleSectionsNotBareStalks ≡ true

    consumerReductionCollapsesPhysicalHyperfabric : Bool
    consumerReductionCollapsesPhysicalHyperfabricIsFalse :
      consumerReductionCollapsesPhysicalHyperfabric ≡ false

    symmetryEquivarianceAloneAuthorizesSectionQuotient : Bool
    symmetryEquivarianceAloneAuthorizesSectionQuotientIsFalse :
      symmetryEquivarianceAloneAuthorizesSectionQuotient ≡ false

    canonicalFutureSafetyImpliesMechanisticRealization : Bool
    canonicalFutureSafetyImpliesMechanisticRealizationIsFalse :
      canonicalFutureSafetyImpliesMechanisticRealization ≡ false

canonicalHyperfabricConsumerReductionBoundary :
  HyperfabricConsumerReductionBoundary
canonicalHyperfabricConsumerReductionBoundary =
  hyperfabric-consumer-reduction-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
