{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBackgroundHessianMetricVariationBoundaryRound105Exact where

------------------------------------------------------------------------
-- ROUND105 CROSS-POLLINATION BOUNDARY
--
-- Round103 proves an exact SAME-OBJECT background-B Hessian identity:
--
--   Pi = D_B^2 V_eff = finite sum of CMP116 physical composite B-Hessians.
--
-- The QFT/GR stress-energy weld, however, needs variation with respect to the
-- spacetime metric/source.  A gauge-background second variation is not that
-- metric variation by naming or dimensional analogy alone.
--
-- This owner therefore makes the missing transport explicit.  Applications may
-- prove a map from metric perturbations into the literal Round103 background
-- calculus, but the map and its commuting theorem are separate physical data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier

record MetricVariationTransport
    (dataSet : Carrier.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    MetricPerturbation : Set
    MetricVariationValue : Set

    metricVariation :
      Source.Background (Carrier.source dataSet) →
      MetricPerturbation → MetricVariationValue

    metricPerturbationToBackgroundTangent :
      Source.Background (Carrier.source dataSet) →
      MetricPerturbation →
      Source.Tangent (Carrier.source dataSet)

    backgroundHessianReadout :
      Source.Background (Carrier.source dataSet) →
      Source.Tangent (Carrier.source dataSet) →
      Source.Tangent (Carrier.source dataSet) →
      MetricVariationValue

    -- This is the genuine bridge theorem.  It is intentionally not derived
    -- from the Round103 B-Hessian equality alone.
    metricVariationFactorsThroughBackgroundCalculus :
      ∀ background metricPerturbation →
      metricVariation background metricPerturbation
      ≡
      backgroundHessianReadout
        background
        (metricPerturbationToBackgroundTangent background metricPerturbation)
        (metricPerturbationToBackgroundTangent background metricPerturbation)

open MetricVariationTransport public

record BackgroundHessianMetricVariationBoundary : Set where
  constructor backgroundHessianMetricVariationBoundary
  field
    cmp109BackgroundHessianIsMetricVariationByDefinition : Bool
    cmp109BackgroundHessianIsMetricVariationByDefinitionIsFalse :
      cmp109BackgroundHessianIsMetricVariationByDefinition ≡ false

    cmp109PolarizationIsStressTensorByDefinition : Bool
    cmp109PolarizationIsStressTensorByDefinitionIsFalse :
      cmp109PolarizationIsStressTensorByDefinition ≡ false

    substitutionCurvatureMayBeDroppedWithoutProof : Bool
    substitutionCurvatureMayBeDroppedWithoutProofIsFalse :
      substitutionCurvatureMayBeDroppedWithoutProof ≡ false

    explicitMetricTransportCanReuseRound103SameObjectCarrier : Bool
    explicitMetricTransportCanReuseRound103SameObjectCarrierIsTrue :
      explicitMetricTransportCanReuseRound103SameObjectCarrier ≡ true

canonicalBackgroundHessianMetricVariationBoundary :
  BackgroundHessianMetricVariationBoundary
canonicalBackgroundHessianMetricVariationBoundary =
  backgroundHessianMetricVariationBoundary
    false refl
    false refl
    false refl
    true refl

round103BackgroundHessianSameObjectLevel : ProofLevel
round103BackgroundHessianSameObjectLevel =
  Carrier.cmp109CMP116PhysicalHessianIdentityLevel

metricVariationTransportFromRound103Level : ProofLevel
metricVariationTransportFromRound103Level = conditional
