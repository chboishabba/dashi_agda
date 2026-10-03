{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136CompletedFourDiagonalExpectationExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

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
      Continuum.FourAdmittedMetricDirections
        (R134.presentCutCanonicalMetricDomain metricInputs))
  where

  metricWeld : R130.ContinuumMetricStressPairingWeld lane
  metricWeld = R136.metricPairing recovery

  completedReadout :
    Domain.MetricPerturbation
      (R134.presentCutCanonicalMetricDomain metricInputs) → ℚ
  completedReadout h =
    Continuum.rationalReadout recovery selected directions
      (R130.continuumValueToPairingScalar metricWeld
        (R114.cmp119CompletedResponse
          (R130.selectedCoordinate metricWeld)
          (R130.metricPerturbationToNuclearTest metricWeld h)))

  completedReadoutIsContinuumReadout :
    ∀ h →
    Domain.AdmissibleMetricPerturbation
      (R134.presentCutCanonicalMetricDomain metricInputs) h →
    completedReadout h
    ≡ Continuum.continuumReadout recovery selected directions h
  completedReadoutIsContinuumReadout h admissible =
    trans
      (cong
        (Continuum.rationalReadout recovery selected directions)
        (R130.completedStressFunctionalEqualsCanonicalStressPairing
          metricWeld h admissible))
      (sym
        (Continuum.continuumReadoutIsLiteralStress
          recovery selected directions h admissible))

  completedFourDiagonalExpectation : ℚ
  completedFourDiagonalExpectation =
    (completedReadout (Continuum.h00 directions)
      + completedReadout (Continuum.h11 directions))
    +
    (completedReadout (Continuum.h22 directions)
      + completedReadout (Continuum.h33 directions))

  completedFourDiagonalExpectationIsR136Response :
    completedFourDiagonalExpectation
    ≡ Continuum.continuumFourDiagonalResponse
        recovery selected directions
  completedFourDiagonalExpectationIsR136Response =
    cong₂ _+_
      (cong₂ _+_
        (completedReadoutIsContinuumReadout
          (Continuum.h00 directions) (Continuum.h00Admissible directions))
        (completedReadoutIsContinuumReadout
          (Continuum.h11 directions) (Continuum.h11Admissible directions)))
      (cong₂ _+_
        (completedReadoutIsContinuumReadout
          (Continuum.h22 directions) (Continuum.h22Admissible directions))
        (completedReadoutIsContinuumReadout
          (Continuum.h33 directions) (Continuum.h33Admissible directions)))

completedExpectationToR136TraceNoLongerIndependentLeaf : Bool
completedExpectationToR136TraceNoLongerIndependentLeaf = true

remainingBLeafIsFiniteAbsoluteExpectationAnchor : Bool
remainingBLeafIsFiniteAbsoluteExpectationAnchor = true
