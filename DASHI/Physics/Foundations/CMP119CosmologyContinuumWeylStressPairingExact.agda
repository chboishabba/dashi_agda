{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact where

------------------------------------------------------------------------
-- SAME GENERATED ACTION: FOUR CONTINUUM METRIC VARIATIONS = LITERAL STRESS.
--
-- R136 already proves, for the recovered generated-action sector,
--
--   continuumFirstVariation[h] = <T_cont , h>
--
-- in the native PairingScalar of the canonical metric stress representation.
-- R119/R118 already provide the explicit PairingScalar -> rational CMP119
-- convention map.  This module simply takes FOUR admitted metric directions
-- and proves the rational four-direction continuum sum is exactly the rational
-- sum of pairings with the SAME literal continuum stress tensor.
--
-- This is a continuum EUCLIDEAN metric-response theorem. It is NOT yet:
--   * identification of these directions with an orthonormal Lorentzian frame,
--   * a renormalized trace-anomaly theorem,
--   * a proof of Wick/OS continuation,
--   * a vacuum-state theorem,
--   * or an FLRW solution.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as R131
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record FourAdmittedMetricDirections
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    : Set₁ where
  field
    h00 h11 h22 h33 : Domain.MetricPerturbation domain

    h00Admissible : Domain.AdmissibleMetricPerturbation domain h00
    h11Admissible : Domain.AdmissibleMetricPerturbation domain h11
    h22Admissible : Domain.AdmissibleMetricPerturbation domain h22
    h33Admissible : Domain.AdmissibleMetricPerturbation domain h33

open FourAdmittedMetricDirections public

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane}
    (recovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        (R134.presentCutCanonicalMetricDomain metricInputs)
        representation coordinate)
    (directions :
      FourAdmittedMetricDirections
        (R134.presentCutCanonicalMetricDomain metricInputs))
  where

  domain = R134.presentCutCanonicalMetricDomain metricInputs

  rationalReadout :
    StressRep.PairingScalar representation → ℚ
  rationalReadout =
    R118.readoutToRational
      (R119.asRound118CanonicalMetricWeld selected)

  continuumReadout :
    Domain.MetricPerturbation domain → ℚ
  continuumReadout h =
    rationalReadout
      (R131.continuumSectorFirstVariation
        (R136.asCommonMetricReadyBalabanSectorRecovery recovery) h)

  literalStressReadout :
    Domain.MetricPerturbation domain → ℚ
  literalStressReadout h =
    rationalReadout
      (StressRep.stressMetricPairing representation
        (StressRep.stressTensor representation) h)

  continuumReadoutIsLiteralStress :
    ∀ h →
    Domain.AdmissibleMetricPerturbation domain h →
    continuumReadout h ≡ literalStressReadout h
  continuumReadoutIsLiteralStress h admissible =
    cong rationalReadout
      (R136.continuumFirstVariationOfUnifiedGeneratedActionIsLiteralStressPairing
        recovery h admissible)

  continuumFourDiagonalResponse : ℚ
  continuumFourDiagonalResponse =
    (continuumReadout (h00 directions)
      + continuumReadout (h11 directions))
    +
    (continuumReadout (h22 directions)
      + continuumReadout (h33 directions))

  literalStressFourDiagonalPairing : ℚ
  literalStressFourDiagonalPairing =
    (literalStressReadout (h00 directions)
      + literalStressReadout (h11 directions))
    +
    (literalStressReadout (h22 directions)
      + literalStressReadout (h33 directions))

  continuumFourDiagonalResponseIsLiteralStressPairing :
    continuumFourDiagonalResponse
    ≡ literalStressFourDiagonalPairing
  continuumFourDiagonalResponseIsLiteralStressPairing =
    let
      e00 =
        continuumReadoutIsLiteralStress
          (h00 directions) (h00Admissible directions)
      e11 =
        continuumReadoutIsLiteralStress
          (h11 directions) (h11Admissible directions)
      e22 =
        continuumReadoutIsLiteralStress
          (h22 directions) (h22Admissible directions)
      e33 =
        continuumReadoutIsLiteralStress
          (h33 directions) (h33Admissible directions)
    in
    trans
      (cong
        (λ x →
          (x + continuumReadout (h11 directions))
          +
          (continuumReadout (h22 directions)
            + continuumReadout (h33 directions)))
        e00)
      (trans
        (cong
          (λ x →
            (literalStressReadout (h00 directions) + x)
            +
            (continuumReadout (h22 directions)
              + continuumReadout (h33 directions)))
          e11)
        (trans
          (cong
            (λ x →
              (literalStressReadout (h00 directions)
                + literalStressReadout (h11 directions))
              +
              (x + continuumReadout (h33 directions)))
            e22)
          (cong
            (λ x →
              (literalStressReadout (h00 directions)
                + literalStressReadout (h11 directions))
              +
              (literalStressReadout (h22 directions) + x))
            e33)))
