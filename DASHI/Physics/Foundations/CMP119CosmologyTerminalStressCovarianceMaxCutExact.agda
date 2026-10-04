{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyTerminalStressCovarianceMaxCutExact where

------------------------------------------------------------------------
-- TERMINAL ANTIGRAVITY MAX-CUT ON THE CURRENT CMP119/R136/R144 ROUTE.
--
-- Euclidean side is no longer free:
--   literalContinuumFourDirectionTrace
-- is the SAME literal continuum stress pairing supplied by R136 and
-- CMP119CosmologyContinuumWeylStressPairingExact.
--
-- Lorentz symmetry side is no longer free numerical algebra:
--   SelectedStressTensorBoostCovariance
-- identifies the boosted selected T01 expectation with the exact rank-two
-- Lorentz action computed in CMP119CosmologySelectedBoostTensorActionExact.
--
-- Therefore the only two physical producer laws left at this cut are:
--
--   (A) selected CMP119 renormalized stress operator covariance under the
--       explicit nontrivial reconstructed boost;
--   (B) same-object continuation from the literal Euclidean continuum trace
--       pairing to the Lorentzian trace of that same selected stress tensor.
--
-- Given those, reconstructed-vacuum invariance and isotropy compile to
-- p = -rho, and positive rho compiles to negative active stress.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_; -_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyContinuumStressPoincareMaxCutExact as ContinuumCut
import DASHI.Physics.Foundations.CMP119CosmologySelectedStressTensorCovarianceCompilerExact as Covariance
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

  literalContinuumTrace : ℚ
  literalContinuumTrace =
    Continuum.literalStressFourDiagonalPairing
      recovery selected directions

  record TerminalStressCovarianceMaxCut
      (Operator : Set) : Set₁ where
    field
      selectedStressCovariance :
        Covariance.SelectedStressTensorBoostCovariance Operator

      sameObjectEuclideanLorentzianTrace :
        Vacuum.trace
          (Covariance.lorentzianIsotropicStress selectedStressCovariance)
        ≡
        literalContinuumTrace

  open TerminalStressCovarianceMaxCut public

  asContinuumStressPoincareMaxCut :
    ∀ {Operator} →
    TerminalStressCovarianceMaxCut Operator →
    ContinuumCut.ContinuumStressPoincareMaxCut
      recovery selected directions Operator
  asContinuumStressPoincareMaxCut cut = record
    { ContinuumCut.ContinuumStressPoincareMaxCut.boostExpectationData =
        Covariance.asSelectedStressBoostExpectationData
          (selectedStressCovariance cut)
    ; ContinuumCut.ContinuumStressPoincareMaxCut.sameObjectTraceContinuation =
        sameObjectEuclideanLorentzianTrace cut
    }

  terminalMaxCutForcesVacuumEquationOfState :
    ∀ {Operator}
      (cut : TerminalStressCovarianceMaxCut Operator) →
    Vacuum.pressure
      (Covariance.lorentzianIsotropicStress
        (selectedStressCovariance cut))
    ≡
    - Vacuum.rho
      (Covariance.lorentzianIsotropicStress
        (selectedStressCovariance cut))
  terminalMaxCutForcesVacuumEquationOfState cut =
    ContinuumCut.continuumStressMaxCutForcesVacuumEquationOfState
      recovery selected directions
      (asContinuumStressPoincareMaxCut cut)

  terminalMaxCutPositiveRhoGivesNegativeActive :
    ∀ {Operator}
      (cut : TerminalStressCovarianceMaxCut Operator) →
    0ℚ <
      Vacuum.rho
        (Covariance.lorentzianIsotropicStress
          (selectedStressCovariance cut)) →
    Vacuum.activeStress
      (Covariance.lorentzianIsotropicStress
        (selectedStressCovariance cut))
    < 0ℚ
  terminalMaxCutPositiveRhoGivesNegativeActive cut positiveRho =
    ContinuumCut.continuumStressMaxCutPositiveRhoGivesNegativeActive
      recovery selected directions
      (asContinuumStressPoincareMaxCut cut)
      positiveRho

  terminalMaxCutPhysicalProducerCount : ℚ
  terminalMaxCutPhysicalProducerCount = 2

  operatorCovarianceProducerStillRequired : Bool
  operatorCovarianceProducerStillRequired = true

  euclideanLorentzianSameObjectContinuationStillRequired : Bool
  euclideanLorentzianSameObjectContinuationStillRequired = true
