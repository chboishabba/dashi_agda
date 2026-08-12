module DASHI.Foundations.CantorUnitMassDynamicBridgeExact where

------------------------------------------------------------------------
-- CANTOR UNIT MASS + DYNAMIC SUFFICIENCY
--
-- Existing modules already separate:
--   * finite Cantor ambient/surviving counts,
--   * consumer-indexed normalized epistemic mass,
--   * dynamic trace-congruence.
--
-- This bridge makes the conjunction explicit.  Unit retained task mass is a
-- static/model-relative certificate; it becomes a safe compression only when
-- paired with a dynamic quotient-safety proof.  Otherwise an exact reopening
-- residual is the fail-closed alternative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ConsumerProjectionSufficiency as Sufficiency
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.ProvenanceBearingQuotient as PBQ
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Foundations.CantorConsumerRelevanceReference as Cantor

record UnitMassDynamicCertificate
    {State Action Observation Consumer Region Mass : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (measure : Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass)
    (consumer : Consumer) : Set₁ where
  constructor unitMassDynamicCertificate
  field
    unitMass :
      Sufficiency.ConsumerMassCertificate measure consumer
    futureSafe :
      Dynamic.DynamicConsumerSafety system project

open UnitMassDynamicCertificate public

toConsumerSafeCompression :
  ∀ {State Action Observation Consumer Region Mass}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {measure : Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass}
    {consumer : Consumer} →
  UnitMassDynamicCertificate system project measure consumer →
  Sufficiency.ConsumerSafeCompression system project measure consumer
toConsumerSafeCompression certificate =
  Sufficiency.consumerSafeCompression
    (unitMass certificate)
    (futureSafe certificate)

record UnitRecoverableProjection
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor unitRecoverableProjection
  field
    quotient : PBQ.ProvenanceBearingQuotient core
    coarseStatePlusReceiptReopens :
      (x : Fibre.Carrier core) →
      PBQ.reopen quotient
        (Fibre.project core x)
        (PBQ.receipt quotient x)
      ≡ x

open UnitRecoverableProjection public

unitTaskMassClaimsWorldTruth : Bool
unitTaskMassClaimsWorldTruth = false

unitTaskMassClaimsWorldTruthIsFalse :
  unitTaskMassClaimsWorldTruth ≡ false
unitTaskMassClaimsWorldTruthIsFalse = refl

depthThreeCantorAmbientVsSurviving :
  Cantor.ambientTernaryCellCount (Cantor.canonicalCantorInquiryStage 3) ≡ 27
depthThreeCantorAmbientVsSurviving = Cantor.depthThreeAmbientCount

depthThreeCantorRetainedTaskMass :
  Relevance.FullRetainedModelMass (Cantor.cantorStageAccounting 3)
depthThreeCantorRetainedTaskMass =
  Cantor.cantorStageRetainsUnitRelevanceMass 3
