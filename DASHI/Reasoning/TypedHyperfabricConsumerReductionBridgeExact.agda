module DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as Canonical
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Consumer
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as FutureCanonical

------------------------------------------------------------------------
-- TYPED HYPERFABRIC -> SET-SIZED SELECTED-SECTION CONSUMER REDUCTION
--
-- Hyperfabric.GlobalSection fabric : Set₁, while ConsumerRelativeReduction is
-- currently parameterised by Fine : Set.  Agda universes are not silently
-- cumulative, so a generic GlobalSection cannot simply be supplied as Fine.
--
-- A domain must instead declare an explicit Set-sized selected-section code
-- and a realization map into actual compatible GlobalSections.  Consumer
-- reduction then acts on those codes.  This preserves the TypedHyperfabric
-- ownership of compatibility while avoiding a parallel sheaf kernel or an
-- unnecessary universe-generalisation of the reduction stack.
------------------------------------------------------------------------

record SelectedSectionCarrier
    {Vertex Edge : Set}
    (fabric : Hyperfabric.TypedHyperfabric Vertex Edge) : Set₁ where
  constructor selected-section-carrier
  field
    SectionCode : Set
    realizeSection : SectionCode → Hyperfabric.GlobalSection fabric
    carrierLabel : String

open SelectedSectionCarrier public

record HyperfabricSectionReduction
    {Vertex Edge Action Observation : Set}
    (fabric : Hyperfabric.TypedHyperfabric Vertex Edge) : Set₁ where
  constructor hyperfabric-section-reduction
  field
    selectedSections : SelectedSectionCarrier fabric
    sectionReduction :
      Reduction.ConsumerRelativeReduction
        (SectionCode selectedSections)
        Action
        Observation
    bridgeReceipt : String

open HyperfabricSectionReduction public

sectionCurrentConsumerDescent :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (bridge : HyperfabricSectionReduction {Action = Action} {Observation = Observation} fabric) →
  Consumer.ConsumerDescent
    (Reduction.encode (sectionReduction bridge))
    (Reduction.fineObserve (sectionReduction bridge))
sectionCurrentConsumerDescent bridge =
  Canonical.currentConsumerDescent (sectionReduction bridge)

sectionActionIntertwiner :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (bridge : HyperfabricSectionReduction {Action = Action} {Observation = Observation} fabric) →
  (action : Action) →
  Consumer.Intertwiner
    (Reduction.encode (sectionReduction bridge))
    (Reduction.encode (sectionReduction bridge))
    (Reduction.fineStep (sectionReduction bridge) action)
    (Reduction.reducedStep (sectionReduction bridge) action)
sectionActionIntertwiner bridge =
  Canonical.actionIntertwiner (sectionReduction bridge)

sectionCanonicalFutureSafety :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (bridge : HyperfabricSectionReduction {Action = Action} {Observation = Observation} fabric) →
  (actionLabel : Action → String) →
  Future.FutureLanguageSafeProjection
    (FutureCanonical.deterministicSystem
      (Reduction.fineStep (sectionReduction bridge)) actionLabel)
    (Reduction.fineObserve (sectionReduction bridge))
    (Reduction.encode (sectionReduction bridge))
sectionCanonicalFutureSafety bridge =
  Canonical.canonicalFutureSafety (sectionReduction bridge)

sectionCodeConsumerFuturePreserved :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    (bridge : HyperfabricSectionReduction {Action = Action} {Observation = Observation} fabric) →
  (actions : List Action) →
  (sectionCode : SectionCode (selectedSections bridge)) →
  Reduction.fineObserve (sectionReduction bridge)
    (Reduction.run (Reduction.fineStep (sectionReduction bridge)) actions sectionCode)
  ≡
  Reduction.reducedObserve (sectionReduction bridge)
    (Reduction.run
      (Reduction.reducedStep (sectionReduction bridge))
      actions
      (Reduction.encode (sectionReduction bridge) sectionCode))
sectionCodeConsumerFuturePreserved bridge =
  Reduction.consumerFuturePreserved (sectionReduction bridge)

sectionCodeEqualityPreservesDeclaredConsumerFuture :
  ∀ {Vertex Edge Action Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    (bridge : HyperfabricSectionReduction {Action = Action} {Observation = Observation} fabric) →
  {left right : SectionCode (selectedSections bridge)} →
  Reduction.encode (sectionReduction bridge) left
    ≡ Reduction.encode (sectionReduction bridge) right →
  (actions : List Action) →
  Reduction.fineObserve (sectionReduction bridge)
    (Reduction.run (Reduction.fineStep (sectionReduction bridge)) actions left)
  ≡
  Reduction.fineObserve (sectionReduction bridge)
    (Reduction.run (Reduction.fineStep (sectionReduction bridge)) actions right)
sectionCodeEqualityPreservesDeclaredConsumerFuture bridge =
  Reduction.encodedEqualityImpliesConsumerFutureEquality (sectionReduction bridge)

------------------------------------------------------------------------
-- Finite exact specimen.
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

data SpecSectionCode : Set where
  leftCode : SpecSectionCode
  rightCode : SpecSectionCode

realizeSpecSection : SpecSectionCode → Hyperfabric.GlobalSection specFabric
realizeSpecSection leftCode = leftSection
realizeSpecSection rightCode = rightSection

specSelectedSections : SelectedSectionCarrier specFabric
specSelectedSections = selected-section-carrier
  SpecSectionCode
  realizeSpecSection
  "two explicit compatible global sections"

sectionVisible : SpecSectionCode → Bool
sectionVisible code =
  proj₁ (Hyperfabric.vertexValue (realizeSpecSection code) region)

specReduction : Reduction.ConsumerRelativeReduction SpecSectionCode ⊤ Bool
specReduction = Reduction.consumerRelativeReduction
  Bool
  sectionVisible
  (λ _ code → code)
  (λ _ visible → visible)
  sectionVisible
  (λ visible → visible)
  (λ _ _ → refl)
  (λ _ → refl)

specBridge : HyperfabricSectionReduction {Action = ⊤} {Observation = Bool} specFabric
specBridge = hyperfabric-section-reduction
  specSelectedSections
  specReduction
  "Set-sized selected-section codes bridge compatible global sections to the canonical consumer-reduction kernel"

hiddenStalkDifferenceCanCollapseForDeclaredConsumer :
  Reduction.encode specReduction leftCode
  ≡ Reduction.encode specReduction rightCode
hiddenStalkDifferenceCanCollapseForDeclaredConsumer = refl

finiteSectionConsumerDescent :
  Consumer.ConsumerDescent
    (Reduction.encode specReduction)
    (Reduction.fineObserve specReduction)
finiteSectionConsumerDescent = sectionCurrentConsumerDescent specBridge

finiteSectionFutureSafe :
  Future.FutureLanguageSafeProjection
    (FutureCanonical.deterministicSystem
      (Reduction.fineStep specReduction)
      (λ _ → "identity section-code action"))
    (Reduction.fineObserve specReduction)
    (Reduction.encode specReduction)
finiteSectionFutureSafe =
  sectionCanonicalFutureSafety specBridge (λ _ → "identity section-code action")

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data SectionCodeEqualityImpliesGlobalSectionIdentity : Set where

sectionCodeEqualityDoesNotImplyGlobalSectionIdentity :
  SectionCodeEqualityImpliesGlobalSectionIdentity → ⊥
sectionCodeEqualityDoesNotImplyGlobalSectionIdentity ()

record HyperfabricConsumerReductionBoundary : Set where
  constructor hyperfabric-consumer-reduction-boundary
  field
    typedHyperfabricOwnsGlobalSectionSemantics : Bool
    selectedSectionCodeMayServeAsFineReductionState : Bool
    globalSectionMayServeDirectlyAsFineReductionState : Bool
    globalSectionMayServeDirectlyAsFineReductionStateIsFalse :
      globalSectionMayServeDirectlyAsFineReductionState ≡ false
    globalSectionUniverseIsNotForcedIntoSet : Bool
    reductionActsOnSelectedCompatibleSectionCodes : Bool
    consumerReductionCollapsesPhysicalHyperfabric : Bool
    consumerReductionCollapsesPhysicalHyperfabricIsFalse :
      consumerReductionCollapsesPhysicalHyperfabric ≡ false
    reducedCodeEqualityImpliesGlobalSectionIdentity : Bool
    reducedCodeEqualityImpliesGlobalSectionIdentityIsFalse :
      reducedCodeEqualityImpliesGlobalSectionIdentity ≡ false
    symmetryEquivarianceAloneAuthorizesSectionQuotient : Bool
    symmetryEquivarianceAloneAuthorizesSectionQuotientIsFalse :
      symmetryEquivarianceAloneAuthorizesSectionQuotient ≡ false
    canonicalFutureSafetyImpliesMechanisticRealization : Bool
    canonicalFutureSafetyImpliesMechanisticRealizationIsFalse :
      canonicalFutureSafetyImpliesMechanisticRealization ≡ false

open HyperfabricConsumerReductionBoundary public

canonicalHyperfabricConsumerReductionBoundary :
  HyperfabricConsumerReductionBoundary
canonicalHyperfabricConsumerReductionBoundary =
  hyperfabric-consumer-reduction-boundary
    true
    true
    false refl
    true
    true
    false refl
    false refl
    false refl
    false refl
