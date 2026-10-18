{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCTerminalMaxCutExact where

------------------------------------------------------------------------
-- PINNED LOCAL-C TERMINAL MAX-CUT.
--
-- This packages the two remaining physical producers on the SAME selected
-- CMP119 object:
--
--   A. boost covariance of LocalC.stressTensor localC in the exact
--      OSR.reconstructedVacuum reconstruction group;
--
--   B. E->L trace continuation of that SAME Local-C stress from the literal
--      R136 four-direction continuum pairing.
--
-- The package compiles directly to the existing terminal stress-covariance
-- max-cut.  No arbitrary operator, vacuum, Euclidean trace scalar, or
-- Lorentzian stress object is selected downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_; -_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCBoostCovarianceExact as BoostLocalC
import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCTraceContinuationExact as TraceLocalC
import DASHI.Physics.Foundations.CMP119CosmologyTerminalStressCovarianceMaxCutExact as Terminal
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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC

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
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
  where

  record PinnedLocalCTerminalProducers : Set₁ where
    field
      boostCovariance :
        BoostLocalC.PinnedLocalCBoostCovariance
          Y group localC

      traceContinuation :
        TraceLocalC.PinnedLocalCTraceContinuation
          recovery selected directions localC boostCovariance

  open PinnedLocalCTerminalProducers public

  asTerminalStressCovarianceMaxCut :
    PinnedLocalCTerminalProducers →
    Terminal.TerminalStressCovarianceMaxCut
      recovery selected directions (Top.StressTensor C)
  asTerminalStressCovarianceMaxCut producers = record
    { Terminal.TerminalStressCovarianceMaxCut.selectedStressCovariance =
        BoostLocalC.asSelectedStressTensorBoostCovariance
          (boostCovariance producers)
    ; Terminal.TerminalStressCovarianceMaxCut.sameObjectEuclideanLorentzianTrace =
        TraceLocalC.isotropicTraceIsLiteralEuclideanTrace
          recovery selected directions localC
          (boostCovariance producers)
          (traceContinuation producers)
    }

  pinnedLocalCTerminalForcesVacuumEquationOfState :
    (producers : PinnedLocalCTerminalProducers) →
    Vacuum.pressure
      (BoostLocalC.lorentzianIsotropicStress
        (boostCovariance producers))
    ≡
    - Vacuum.rho
      (BoostLocalC.lorentzianIsotropicStress
        (boostCovariance producers))
  pinnedLocalCTerminalForcesVacuumEquationOfState producers =
    Terminal.terminalMaxCutForcesVacuumEquationOfState
      recovery selected directions
      (asTerminalStressCovarianceMaxCut producers)

  pinnedLocalCTerminalPositiveRhoGivesNegativeActive :
    (producers : PinnedLocalCTerminalProducers) →
    0ℚ <
      Vacuum.rho
        (BoostLocalC.lorentzianIsotropicStress
          (boostCovariance producers)) →
    Vacuum.activeStress
      (BoostLocalC.lorentzianIsotropicStress
        (boostCovariance producers))
    < 0ℚ
  pinnedLocalCTerminalPositiveRhoGivesNegativeActive
      producers positiveRho =
    Terminal.terminalMaxCutPositiveRhoGivesNegativeActive
      recovery selected directions
      (asTerminalStressCovarianceMaxCut producers)
      positiveRho

  pinnedLocalCVacuum :
    (producers : PinnedLocalCTerminalProducers) →
    Vacuum.VacuumLikeLorentzianStress
  pinnedLocalCVacuum producers = record
    { Vacuum.VacuumLikeLorentzianStress.stress =
        BoostLocalC.lorentzianIsotropicStress
          (boostCovariance producers)
    ; Vacuum.VacuumLikeLorentzianStress.pressureIsMinusRho =
        pinnedLocalCTerminalForcesVacuumEquationOfState producers
    }

  pinnedLocalCLiteralContinuumTraceNegativeGivesNegativeActive :
    (producers : PinnedLocalCTerminalProducers) →
    Continuum.literalStressFourDiagonalPairing
      recovery selected directions < 0ℚ →
    Vacuum.activeStress
      (BoostLocalC.lorentzianIsotropicStress
        (boostCovariance producers))
    < 0ℚ
  pinnedLocalCLiteralContinuumTraceNegativeGivesNegativeActive
      producers literalTraceNegative =
    let
      terminal =
        asTerminalStressCovarianceMaxCut producers

      sameTrace :
        Vacuum.trace
          (BoostLocalC.lorentzianIsotropicStress
            (boostCovariance producers))
        ≡
        Continuum.literalStressFourDiagonalPairing
          recovery selected directions
      sameTrace =
        Terminal.sameObjectEuclideanLorentzianTrace terminal

      lorentzianTraceNegative :
        Vacuum.trace
          (BoostLocalC.lorentzianIsotropicStress
            (boostCovariance producers))
        < 0ℚ
      lorentzianTraceNegative =
        subst
          (λ value → value < 0ℚ)
          (sym sameTrace)
          literalTraceNegative
    in
    Vacuum.vacuumTraceNegativeImpliesActiveNegative
      (pinnedLocalCVacuum producers)
      lorentzianTraceNegative

  pinnedLocalCLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration :
    (positiveGravityFactor : ℚ) →
    (producers : PinnedLocalCTerminalProducers) →
    0ℚ < positiveGravityFactor →
    Continuum.literalStressFourDiagonalPairing
      recovery selected directions < 0ℚ →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (BoostLocalC.lorentzianIsotropicStress
          (boostCovariance producers))
  pinnedLocalCLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      positiveGravityFactor producers factorPositive literalTraceNegative =
    Vacuum.negativeActiveStressGivesPositiveMatterAcceleration
      positiveGravityFactor
      (BoostLocalC.lorentzianIsotropicStress
        (boostCovariance producers))
      factorPositive
      (pinnedLocalCLiteralContinuumTraceNegativeGivesNegativeActive
        producers literalTraceNegative)

  allDownstreamAntigravityAlgebraCompiled : Bool
  allDownstreamAntigravityAlgebraCompiled = true

  remainingPhysicalProducerCount : ℚ
  remainingPhysicalProducerCount = 2
