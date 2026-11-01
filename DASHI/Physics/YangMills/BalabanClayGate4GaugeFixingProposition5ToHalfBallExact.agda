module DASHI.Physics.YangMills.BalabanClayGate4GaugeFixingProposition5ToHalfBallExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact as Construction
import DASHI.Physics.YangMills.BalabanClayGate4HalfContractionInvariantBallExact as HalfBall
import DASHI.Physics.YangMills.BalabanClayGate4BalabanGaugeFixingProposition5Exact as Proposition5

------------------------------------------------------------------------
-- Transport Bałaban Proposition 5 to the common contraction-ball interface.
--
-- The source theorem supplies the half-contraction estimate and preservation of
-- the beta=1/4 domain.  A repository instantiation identifies the source norm,
-- distance, multiplication and order with the selected finite tangent-space
-- metric, and supplies the centre forcing estimate.  The invariant-ball and
-- fixed-point consequences are then generic.
------------------------------------------------------------------------

record GaugeFixingProposition5MetricBridge
    {Configuration Correction Bound : Set}
    (source : Proposition5.BalabanGaugeFixingProposition5
      Configuration Correction Bound)
    (triangle : Construction.MetricTriangleBudget Correction Bound)
    (halfBudget : HalfBall.HalfContractionBudget triangle) : Set₁ where
  field
    configuration : Configuration
    admissible : Proposition5.AdmissibleConfiguration source configuration

    centre : Correction
    radius forcing : Bound

    radiusMeaning :
      radius
      ≡ Proposition5.multiply source
          (Proposition5.quarter source) (Proposition5.alpha4 source)

    halfMeaning :
      HalfBall.half halfBudget ≡ Proposition5.half source

    metricDistanceMeaning : ∀ left right →
      Quantitative.distance (Construction.metric triangle) left right
      ≡ Proposition5.distance source left right

    metricMultiplyMeaning : ∀ left right →
      Quantitative.multiply (Construction.metric triangle) left right
      ≡ Proposition5.multiply source left right

    metricOrderMeaning : ∀ left right →
      Quantitative.LessEqual (Construction.metric triangle) left right
      ≡ Proposition5.LessEqual source left right

    quarterDomainIsMetricBall : ∀ correction →
      Proposition5.InQuarterDomain source correction
      ≡ Quantitative.LessEqual (Construction.metric triangle)
          (Quantitative.distance (Construction.metric triangle)
            correction centre)
          radius

    centreInQuarterDomain :
      Proposition5.InQuarterDomain source centre

    centreDisplacement :
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle)
          (Proposition5.fixedPointMap source configuration centre)
          centre)
        forcing

    forcingBelowHalfRadius :
      Quantitative.LessEqual (Construction.metric triangle)
        forcing (HalfBall.halfRadius halfBudget radius)

    multiplyRadiusMonotone : ∀ value →
      Quantitative.LessEqual (Construction.metric triangle) value radius →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.multiply (Construction.metric triangle)
          (Proposition5.half source) value)
        (Quantitative.multiply (Construction.metric triangle)
          (Proposition5.half source) radius)

open GaugeFixingProposition5MetricBridge public

sourceHalfContractionAsMetric :
  ∀ {Configuration Correction Bound}
    {source : Proposition5.BalabanGaugeFixingProposition5
      Configuration Correction Bound}
    {triangle : Construction.MetricTriangleBudget Correction Bound}
    {halfBudget : HalfBall.HalfContractionBudget triangle}
    (bridge : GaugeFixingProposition5MetricBridge source triangle halfBudget)
    left right →
  Proposition5.InQuarterDomain source left →
  Proposition5.InQuarterDomain source right →
  Quantitative.LessEqual (Construction.metric triangle)
    (Quantitative.distance (Construction.metric triangle)
      (Proposition5.fixedPointMap source (configuration bridge) left)
      (Proposition5.fixedPointMap source (configuration bridge) right))
    (Quantitative.multiply (Construction.metric triangle)
      (Proposition5.half source)
      (Quantitative.distance (Construction.metric triangle) left right))
sourceHalfContractionAsMetric
    {source = source} {triangle = triangle}
    bridge left right leftIn rightIn =
  let sourceLower = Proposition5.distance source
        (Proposition5.fixedPointMap source (configuration bridge) left)
        (Proposition5.fixedPointMap source (configuration bridge) right)
      metricLower = Quantitative.distance (Construction.metric triangle)
        (Proposition5.fixedPointMap source (configuration bridge) left)
        (Proposition5.fixedPointMap source (configuration bridge) right)
      sourceDistance = Proposition5.distance source left right
      metricDistance = Quantitative.distance
        (Construction.metric triangle) left right
      sourceUpper = Proposition5.multiply source
        (Proposition5.half source) sourceDistance
      sourceProof = Proposition5.mapContractsByHalf source
        (configuration bridge) left right
        (admissible bridge) leftIn rightIn
      sameOrderProof = subst
        (λ proposition → proposition)
        (sym (metricOrderMeaning bridge sourceLower sourceUpper))
        sourceProof
      lowerTransport = subst
        (λ lower → Quantitative.LessEqual
          (Construction.metric triangle) lower sourceUpper)
        (sym (metricDistanceMeaning bridge
          (Proposition5.fixedPointMap source (configuration bridge) left)
          (Proposition5.fixedPointMap source (configuration bridge) right)))
        sameOrderProof
      upperMeaning = trans
        (metricMultiplyMeaning bridge
          (Proposition5.half source) metricDistance)
        (cong₂ (Proposition5.multiply source)
          refl (metricDistanceMeaning bridge left right))
  in subst
      (λ upper → Quantitative.LessEqual
        (Construction.metric triangle) metricLower upper)
      (sym upperMeaning)
      lowerTransport

asHalfContractionBall :
  ∀ {Configuration Correction Bound}
    {source : Proposition5.BalabanGaugeFixingProposition5
      Configuration Correction Bound}
    {triangle : Construction.MetricTriangleBudget Correction Bound}
    {halfBudget : HalfBall.HalfContractionBudget triangle} →
  GaugeFixingProposition5MetricBridge source triangle halfBudget →
  HalfBall.HalfContractionBall halfBudget
asHalfContractionBall
    {source = source} {triangle = triangle} {halfBudget = halfBudget}
    bridge = record
  { centre = centre bridge
  ; radius = radius bridge
  ; contraction = Proposition5.half source
  ; forcing = forcing bridge
  ; map =
      Proposition5.fixedPointMap source (configuration bridge)
  ; InBall =
      Proposition5.InQuarterDomain source
  ; inBallMeaning =
      quarterDomainIsMetricBall bridge
  ; centreInBall =
      centreInQuarterDomain bridge
  ; centreDisplacement =
      centreDisplacement bridge
  ; contractionEstimate =
      sourceHalfContractionAsMetric bridge
  ; contractionBelowHalf =
      subst
        (λ upper → Quantitative.LessEqual
          (Construction.metric triangle) (Proposition5.half source) upper)
        (sym (halfMeaning bridge))
        (Quantitative.reflexive
          (Construction.metric triangle) (Proposition5.half source))
  ; forcingBelowHalfRadius =
      forcingBelowHalfRadius bridge
  ; multiplyRadiusMonotone =
      multiplyRadiusMonotone bridge
  }

asInvariantGaugeFixingBall :
  ∀ {Configuration Correction Bound}
    {source : Proposition5.BalabanGaugeFixingProposition5
      Configuration Correction Bound}
    {triangle : Construction.MetricTriangleBudget Correction Bound}
    {halfBudget : HalfBall.HalfContractionBudget triangle} →
  GaugeFixingProposition5MetricBridge source triangle halfBudget →
  Quantitative.InvariantContractionBall (Construction.metric triangle)
asInvariantGaugeFixingBall bridge =
  Construction.asInvariantContractionBall
    (HalfBall.asContractionBallConstruction
      (asHalfContractionBall bridge))

balabanGaugeFixingMetricTransportLevel : ProofLevel
balabanGaugeFixingMetricTransportLevel = machineChecked

balabanGaugeFixingInvariantBallLevel : ProofLevel
balabanGaugeFixingInvariantBallLevel = machineChecked

physicalGaugeFixingMetricIdentificationInputsLevel : ProofLevel
physicalGaugeFixingMetricIdentificationInputsLevel = conditional

physicalGaugeFixingCentreForcingInputsLevel : ProofLevel
physicalGaugeFixingCentreForcingInputsLevel = conditional
