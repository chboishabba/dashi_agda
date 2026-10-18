{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyContinuumStressPoincareMaxCutExact where

------------------------------------------------------------------------
-- REMOVE THE LAST FREE EUCLIDEAN TRACE SCALAR FROM THE ANTIGRAVITY MAX-CUT.
--
-- CMP119CosmologyContinuumWeylStressPairingExact already proves that the
-- recovered generated-action four-direction continuum response is exactly the
-- four-direction pairing of the SAME literal continuum stress tensor.
--
-- This module chooses that literal continuum stress pairing as Q^E in the
-- Poincare-vacuum max-cut.  Therefore the antigravity branch no longer accepts
-- an independently populated Euclidean trace scalar.
--
-- Remaining physical inputs:
--   * a selected Lorentzian isotropic stress on the SAME reconstructed state;
--   * operator/vacuum boost data sufficient to produce the selected boost weld;
--   * same-object continuation from THIS literal continuum stress pairing to
--     the Lorentzian trace.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_; -_)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyPoincareVacuumStressMaxCutExact as MaxCut
import DASHI.Physics.Foundations.CMP119CosmologyVacuumExpectationBoostCompilerExact as Expectation
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum

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

  literalContinuumFourDirectionTrace : ℚ
  literalContinuumFourDirectionTrace =
    Continuum.literalStressFourDiagonalPairing
      recovery selected directions

  continuumResponseIsThisLiteralTrace :
    Continuum.continuumFourDiagonalResponse
      recovery selected directions
    ≡ literalContinuumFourDirectionTrace
  continuumResponseIsThisLiteralTrace =
    Continuum.continuumFourDiagonalResponseIsLiteralStressPairing
      recovery selected directions

  record ContinuumStressPoincareMaxCut
      (Operator : Set) : Set₁ where
    field
      boostExpectationData :
        Expectation.SelectedStressBoostExpectationData Operator

      sameObjectTraceContinuation :
        Vacuum.trace
          (Expectation.lorentzianIsotropicStress boostExpectationData)
        ≡
        literalContinuumFourDirectionTrace

  open ContinuumStressPoincareMaxCut public

  asSelectedCMP119CosmologyMaxCut :
    ∀ {Operator} →
    ContinuumStressPoincareMaxCut Operator →
    MaxCut.SelectedCMP119CosmologyMaxCut
  asSelectedCMP119CosmologyMaxCut cut = record
    { MaxCut.SelectedCMP119CosmologyMaxCut.selectedEuclideanWeylResponse =
        literalContinuumFourDirectionTrace
    ; MaxCut.SelectedCMP119CosmologyMaxCut.boostWeld =
        Expectation.asSelectedPoincareVacuumStressBoostWeld
          (boostExpectationData cut)
    ; MaxCut.SelectedCMP119CosmologyMaxCut.sameObjectTraceContinuation =
        sameObjectTraceContinuation cut
    }

  continuumStressMaxCutForcesVacuumEquationOfState :
    ∀ {Operator}
      (cut : ContinuumStressPoincareMaxCut Operator) →
    Vacuum.pressure
      (Expectation.lorentzianIsotropicStress
        (boostExpectationData cut))
    ≡
    - Vacuum.rho
      (Expectation.lorentzianIsotropicStress
        (boostExpectationData cut))
  continuumStressMaxCutForcesVacuumEquationOfState cut =
    MaxCut.maxCutForcesVacuumEquationOfState
      (asSelectedCMP119CosmologyMaxCut cut)

  continuumStressMaxCutPositiveRhoGivesNegativeActive :
    ∀ {Operator}
      (cut : ContinuumStressPoincareMaxCut Operator) →
    0ℚ <
      Vacuum.rho
        (Expectation.lorentzianIsotropicStress
          (boostExpectationData cut)) →
    Vacuum.activeStress
      (Expectation.lorentzianIsotropicStress
        (boostExpectationData cut))
    < 0ℚ
  continuumStressMaxCutPositiveRhoGivesNegativeActive cut positiveRho =
    MaxCut.maxCutPositiveRhoGivesNegativeActive
      (asSelectedCMP119CosmologyMaxCut cut)
      positiveRho

  continuumStressMaxCutPositiveRhoGivesNegativeLiteralTrace :
    ∀ {Operator}
      (cut : ContinuumStressPoincareMaxCut Operator) →
    0ℚ <
      Vacuum.rho
        (Expectation.lorentzianIsotropicStress
          (boostExpectationData cut)) →
    literalContinuumFourDirectionTrace < 0ℚ
  continuumStressMaxCutPositiveRhoGivesNegativeLiteralTrace cut positiveRho =
    MaxCut.maxCutPositiveRhoGivesNegativeSelectedTrace
      (asSelectedCMP119CosmologyMaxCut cut)
      positiveRho
