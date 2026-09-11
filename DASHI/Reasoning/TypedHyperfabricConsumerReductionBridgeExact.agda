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
-- No new fibre/sheaf/reduction kernel is introduced here.  A compatible
-- Hyperfabric.GlobalSection is simply used as the Fine state of the already
-- canonical ConsumerRelativeReduction kernel.  The reduced state is therefore
-- explicitly a consumer-facing quotient/projection of compatible sections,
-- not a claim that the physical/local fabric itself has collapsed.
------------------------------------------------------------------------

HyperfabricSectionReduction :
  {Vertex Edge : Set} ->
  Hyperfabric.TypedHyperfabric Vertex Edge ->
  Set -> Set -> Set1
HyperfabricSectionReduction fabric Action Observation =
  Reduction.ConsumerRelativeReduction
    (Hyperfabric.GlobalSection fabric)
    Action
    Observation

sectionCurrentConsumerDescent :
  forall {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} ->
  (rom : HyperfabricSectionReduction fabric Action Observation) ->
  Consumer.ConsumerDescent
    (Reduction.encode rom)
    (Reduction.fineObserve rom)
sectionCurrentConsumerDescent = Canonical.currentConsumerDescent

sectionActionIntertwiner :
  forall {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} ->
  (rom : HyperfabricSectionReduction fabric Action Observation) ->
  (action : Action) ->
  Consumer.Intertwiner
    (Reduction.encode rom)
    (Reduction.encode rom)
    (Reduction.fineStep rom action)
    (Reduction.reducedStep rom action)
sectionActionIntertwiner = Canonical.actionIntertwiner

sectionCanonicalFutureSafety :
  forall {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} ->
  (rom : HyperfabricSectionReduction fabric Action Observation) ->
  (actionLabel : Action -> String) ->
  Future.FutureLanguageSafeProjection
    (FutureCanonical.deterministicSystem (Reduction.fineStep rom) actionLabel)
    (Reduction.fineObserve rom)
    (Reduction.encode rom)
sectionCanonicalFutureSafety = Canonical.canonicalFutureSafety

------------------------------------------------------------------------
-- Finite exact specimen.
--
-- One compatible global section carries a visible coordinate and an extra
-- hidden/local coordinate in its vertex stalk.  The declared consumer sees
-- only the visible coordinate.  Two globally compatible sections may then
-- collapse to the same consumer code while remaining distinct local-stalk
-- assignments.  This is consumer quotienting of sections, not stalk identity.
------------------------------------------------------------------------

data SpecVertex : Set where
  region : SpecVertex

data SpecEdge : Set where
  relation : SpecEdge

data SpecIncidence : SpecVertex -> SpecEdge -> Set where
  regionOnRelation : SpecIncidence region relation

specFabric : Hyperfabric.TypedHyperfabric SpecVertex SpecEdge
specFabric = record
  { vertexStalk = lambda _ -> Bool × Bool
  ; edgeStalk = lambda _ -> Bool
  ; incidence = SpecIncidence
  ; restrict = lambda _ pair -> proj1 pair
  ; edgeProvenance = lambda _ -> "finite section-reduction specimen" ∷ []
  ; edgeSalience = lambda _ -> 1
  ; fabricLabel = "finite hyperfabric section consumer-reduction specimen"
  }

leftSection : Hyperfabric.GlobalSection specFabric
leftSection = record
  { vertexValue = lambda _ -> false , false
  ; edgeValue = lambda _ -> false
  ; compatible = lambda _ -> refl
  ; sectionReceipt = "visible=false; hidden=false"
  }

rightSection : Hyperfabric.GlobalSection specFabric
rightSection = record
  { vertexValue = lambda _ -> false , true
  ; edgeValue = lambda _ -> false
  ; compatible = lambda _ -> refl
  ; sectionReceipt = "visible=false; hidden=true"
  }

sectionVisible : Hyperfabric.GlobalSection specFabric -> Bool
sectionVisible section = proj1 (Hyperfabric.vertexValue section region)

specReduction : HyperfabricSectionReduction specFabric ⊤ Bool
specReduction = Reduction.consumerRelativeReduction
  Bool
  sectionVisible
  (lambda _ section -> section)
  (lambda _ code -> code)
  sectionVisible
  (lambda code -> code)
  (lambda _ _ -> refl)
  (lambda _ -> refl)

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
      (lambda _ -> "identity section action"))
    (Reduction.fineObserve specReduction)
    (Reduction.encode specReduction)
finiteSectionFutureSafe =
  sectionCanonicalFutureSafety specReduction (lambda _ -> "identity section action")

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
