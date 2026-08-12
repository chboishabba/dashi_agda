module DASHI.Foundations.CantorConsumerRelevanceReference where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
import DASHI.Biology.TernaryCantorWheelDiffusionExact as Cantor
import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance

------------------------------------------------------------------------
-- Finite Cantor/refinement reference.
--
-- This module formalises only the finite combinatorial analogy needed by ITIR:
-- at refinement depth d the ambient ternary carrier has 3^d cells while the
-- polar/Cantor restriction has 2^d surviving cells, yet a chosen consumer may
-- normalize all of its relevance mass onto the surviving region.
--
-- It does NOT prove the limiting Cantor function, Lebesgue-measure-zero result,
-- Hausdorff dimension, or any classical measure-theory theorem.
------------------------------------------------------------------------

record FiniteCantorInquiryStage (depth : Nat) : Set where
  constructor finiteCantorInquiryStage
  field
    ambientTernaryCellCount : Nat
    survivingPolarCellCount : Nat
    ambientCountExact :
      ambientTernaryCellCount ≡ Cantor.ternaryAddressCount depth
    survivingCountExact :
      survivingPolarCellCount ≡ Cantor.polarAddressCount depth

open FiniteCantorInquiryStage public

canonicalCantorInquiryStage :
  (depth : Nat) → FiniteCantorInquiryStage depth
canonicalCantorInquiryStage depth =
  finiteCantorInquiryStage
    (Cantor.ternaryAddressCount depth)
    (Cantor.polarAddressCount depth)
    refl
    refl

depthThreeAmbientCount :
  ambientTernaryCellCount (canonicalCantorInquiryStage 3) ≡ 27
depthThreeAmbientCount = Cantor.ternaryDepthThreeCount

depthThreeSurvivingCount :
  survivingPolarCellCount (canonicalCantorInquiryStage 3) ≡ 8
depthThreeSurvivingCount = Cantor.polarDepthThreeCount

depthThreeCountsDiffer :
  survivingPolarCellCount (canonicalCantorInquiryStage 3)
  ≡ ambientTernaryCellCount (canonicalCantorInquiryStage 3) → ⊥
depthThreeCountsDiffer ()

------------------------------------------------------------------------
-- Consumer relevance mass on the finite stage.
--
-- The normalized unit means "all relevance represented by this consumer's
-- current model", not "the world is known completely".  Removed/gap structure
-- may carry zero mass for this particular query while the surviving stage
-- carries unit mass.
------------------------------------------------------------------------

data CantorInquiryConsumer : Set where
  survivingStructureConsumer : CantorInquiryConsumer

data CantorInquiryRegion : Set where
  wholeInquiryCarrier : CantorInquiryRegion
  survivingStage : Nat → CantorInquiryRegion
  removedStage : Nat → CantorInquiryRegion
  outsideInquiryModel : CantorInquiryRegion

one : Nat
one = suc zero

cantorRelevanceMass :
  CantorInquiryConsumer → CantorInquiryRegion → Nat
cantorRelevanceMass survivingStructureConsumer wholeInquiryCarrier = one
cantorRelevanceMass survivingStructureConsumer (survivingStage depth) = one
cantorRelevanceMass survivingStructureConsumer (removedStage depth) = zero
cantorRelevanceMass survivingStructureConsumer outsideInquiryModel = zero

cantorRelevanceMeasure :
  Relevance.ConsumerIndexedRelevanceMeasure
    CantorInquiryConsumer CantorInquiryRegion Nat
cantorRelevanceMeasure =
  Relevance.consumerIndexedRelevanceMeasure
    Relevance.consumerRelevanceMass
    wholeInquiryCarrier
    zero
    one
    _+ᶜ_
    cantorRelevanceMass
    (λ consumer → refl)

cantorStageAccounting :
  (depth : Nat) →
  Relevance.OpenWorldMassAccounting
    cantorRelevanceMeasure survivingStructureConsumer
cantorStageAccounting depth =
  Relevance.openWorldMassAccounting
    (survivingStage depth)
    (removedStage depth)
    outsideInquiryModel
    "finite Cantor-stage relevance accounting; removed ambient cells are query-irrelevant"
    refl

cantorStageRetainsUnitRelevanceMass :
  (depth : Nat) →
  Relevance.FullRetainedModelMass (cantorStageAccounting depth)
cantorStageRetainsUnitRelevanceMass depth =
  Relevance.fullRetainedModelMass refl

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record CantorConsumerRelevanceBoundary : Set where
  constructor cantorConsumerRelevanceBoundary
  field
    finiteAmbientAndSurvivingCountsDistinguished : Bool
    finiteAmbientAndSurvivingCountsDistinguishedIsTrue :
      finiteAmbientAndSurvivingCountsDistinguished ≡ true
    survivingRegionMayCarryUnitTaskMass : Bool
    survivingRegionMayCarryUnitTaskMassIsTrue :
      survivingRegionMayCarryUnitTaskMass ≡ true
    limitingCantorMeasureTheoremProvedHere : Bool
    limitingCantorMeasureTheoremProvedHereIsFalse :
      limitingCantorMeasureTheoremProvedHere ≡ false
    unitTaskMassClaimsObjectiveTruth : Bool
    unitTaskMassClaimsObjectiveTruthIsFalse :
      unitTaskMassClaimsObjectiveTruth ≡ false

open CantorConsumerRelevanceBoundary public

canonicalCantorConsumerRelevanceBoundary : CantorConsumerRelevanceBoundary
canonicalCantorConsumerRelevanceBoundary =
  cantorConsumerRelevanceBoundary
    true refl
    true refl
    false refl
    false refl
