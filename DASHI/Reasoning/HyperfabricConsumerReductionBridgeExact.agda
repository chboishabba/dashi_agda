module DASHI.Reasoning.HyperfabricConsumerReductionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction

------------------------------------------------------------------------
-- HYPERFABRIC GLOBAL SECTION -> SET-SIZED CONSUMER REDUCTION BRIDGE
--
-- TypedHyperfabric.GlobalSection fabric lives in Set₁, while the existing
-- ConsumerRelativeReduction kernel is intentionally Set-sized.  We therefore
-- do not force the generic GlobalSection universe downward and do not
-- universe-generalise the reduction kernel here.
--
-- Instead, a domain declares an explicit Set-sized selected-section code and a
-- realization map into actual compatible global sections.  Consumer reduction
-- is then certified on that selected code carrier.  This is the formal shape
-- needed by finite/declared charts such as the MaleCNS observational chart.
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

------------------------------------------------------------------------
-- Existing reduction theorems lift directly once the Fine carrier is the
-- declared Set-sized section code.
------------------------------------------------------------------------

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
-- Promotion firewalls.
--
-- Equality after the consumer reduction is an observational/future-consumer
-- statement.  It is not authority to identify the realized physical/global
-- sections, their path provenance, or their mechanism.
------------------------------------------------------------------------

data SectionCodeEqualityImpliesGlobalSectionIdentity : Set where

sectionCodeEqualityDoesNotImplyGlobalSectionIdentity :
  SectionCodeEqualityImpliesGlobalSectionIdentity → ⊥
sectionCodeEqualityDoesNotImplyGlobalSectionIdentity ()

record HyperfabricConsumerReductionBoundary : Set where
  constructor hyperfabric-consumer-reduction-boundary
  field
    typedHyperfabricOwnsGlobalSectionSemantics : Bool
    selectedSectionCodeIsExplicitSetSizedCarrier : Bool
    globalSectionUniverseIsNotForcedIntoSet : Bool
    consumerReductionRunsOnSelectedSectionCode : Bool
    reducedEqualityImpliesConsumerFutureEquality : Bool
    reducedEqualityImpliesGlobalSectionIdentity : Bool
    reducedEqualityImpliesGlobalSectionIdentityIsFalse :
      reducedEqualityImpliesGlobalSectionIdentity ≡ false
    reducedEqualityImpliesMechanismIdentity : Bool
    reducedEqualityImpliesMechanismIdentityIsFalse :
      reducedEqualityImpliesMechanismIdentity ≡ false
    bridgeAutomaticallyConstructsMaleCNSPhysicalIncidence : Bool
    bridgeAutomaticallyConstructsMaleCNSPhysicalIncidenceIsFalse :
      bridgeAutomaticallyConstructsMaleCNSPhysicalIncidence ≡ false
    boundaryNote : String

open HyperfabricConsumerReductionBoundary public

canonicalHyperfabricConsumerReductionBoundary :
  HyperfabricConsumerReductionBoundary
canonicalHyperfabricConsumerReductionBoundary =
  hyperfabric-consumer-reduction-boundary
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "TypedHyperfabric retains the physical/local compatible-section semantics. A declared Set-sized section code may be reduced for one consumer, but consumer-future equivalence does not collapse realized global-section identity, path provenance, mechanism, or physical topology."
