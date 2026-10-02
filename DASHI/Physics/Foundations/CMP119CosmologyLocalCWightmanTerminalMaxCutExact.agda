{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact where

------------------------------------------------------------------------
-- TERMINAL MAX-CUT THROUGH ONE LOCAL-C -> WIGHTMAN STRESS HINGE.
--
-- One selected Lorentzian stress operator is shared by both remaining physics:
--
--   selectedLorentzianStress
--     = continueLocalCStress (LocalC.stressTensor localC).
--
-- Producer A supplies, for this same operator on the pinned reconstructed
-- vacuum, isotropic rest T01 = 0, vacuum invariance under the selected boost,
-- and rank-two boost covariance.
--
-- Producer B supplies, for this same operator on the same pinned vacuum, the
-- Lorentzian trace readout and its equality with the literal R136 Euclidean
-- four-direction stress pairing.
--
-- The generic terminal compiler then gives
--
--   p = -rho
--   and
--   rho > 0 -> rho + 3p < 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_; -_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact as Hinge
import DASHI.Physics.Foundations.CMP119CosmologySelectedBoostTensorActionExact as Tensor
import DASHI.Physics.Foundations.CMP119CosmologySelectedStressTensorCovarianceCompilerExact as Covariance
import DASHI.Physics.Foundations.CMP119CosmologyTerminalStressCovarianceMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR

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
    (hinge :
      Hinge.LocalCWightmanStressHinge
        Y group localC)
  where

  literalEuclideanTrace : ℚ
  literalEuclideanTrace =
    Continuum.literalStressFourDiagonalPairing
      recovery selected directions

  record LocalCWightmanTerminalProducers : Set₁ where
    field
      lorentzianIsotropicStress :
        Vacuum.IsotropicLorentzianStress

      -- Producer A: exact selected-operator covariance on the exact OS vacuum.
      restT01ExpectationZero :
        Hinge.stress01Expectation hinge
          (OSR.reconstructedVacuum reconstruction group)
          (Hinge.selectedLorentzianStress hinge)
        ≡ 0ℚ

      reconstructedVacuumBoostInvariantOnT01 :
        Hinge.stress01Expectation hinge
          (OSR.reconstructedVacuum reconstruction group)
          (Hinge.boostConjugate hinge
            (Hinge.selectedLorentzianStress hinge))
        ≡
        Hinge.stress01Expectation hinge
          (OSR.reconstructedVacuum reconstruction group)
          (Hinge.selectedLorentzianStress hinge)

      selectedStressTransformsAsRankTwoTensor :
        Hinge.stress01Expectation hinge
          (OSR.reconstructedVacuum reconstruction group)
          (Hinge.boostConjugate hinge
            (Hinge.selectedLorentzianStress hinge))
        ≡
        Tensor.t01
          (Tensor.boostBlock01
            (Tensor.isotropicRestBlock lorentzianIsotropicStress))

      -- Producer B: trace of that SAME continued operator equals both the
      -- isotropic Lorentzian trace and the literal R136 Euclidean trace.
      continuedTraceIsIsotropicTrace :
        Hinge.lorentzianTraceExpectation hinge
          (OSR.reconstructedVacuum reconstruction group)
          (Hinge.selectedLorentzianStress hinge)
        ≡
        Vacuum.trace lorentzianIsotropicStress

      continuedTraceIsLiteralR136Trace :
        Hinge.lorentzianTraceExpectation hinge
          (OSR.reconstructedVacuum reconstruction group)
          (Hinge.selectedLorentzianStress hinge)
        ≡
        literalEuclideanTrace

  open LocalCWightmanTerminalProducers public

  asSelectedStressTensorBoostCovariance :
    LocalCWightmanTerminalProducers →
    Covariance.SelectedStressTensorBoostCovariance
      (Hinge.LorentzianStressOperator hinge)
  asSelectedStressTensorBoostCovariance producers = record
    { Covariance.SelectedStressTensorBoostCovariance.lorentzianIsotropicStress =
        lorentzianIsotropicStress producers
    ; Covariance.SelectedStressTensorBoostCovariance.selectedT01 =
        Hinge.selectedLorentzianStress hinge
    ; Covariance.SelectedStressTensorBoostCovariance.boostConjugate =
        Hinge.boostConjugate hinge
    ; Covariance.SelectedStressTensorBoostCovariance.vacuumExpectation =
        Hinge.stress01Expectation hinge
          (OSR.reconstructedVacuum reconstruction group)
    ; Covariance.SelectedStressTensorBoostCovariance.unboostedT01ExpectationZero =
        restT01ExpectationZero producers
    ; Covariance.SelectedStressTensorBoostCovariance.reconstructedVacuumExpectationInvariant =
        reconstructedVacuumBoostInvariantOnT01 producers
    ; Covariance.SelectedStressTensorBoostCovariance.boostedT01ExpectationIsTensorAction =
        selectedStressTransformsAsRankTwoTensor producers
    }

  sameObjectTraceContinuation :
    (producers : LocalCWightmanTerminalProducers) →
    Vacuum.trace (lorentzianIsotropicStress producers)
    ≡ literalEuclideanTrace
  sameObjectTraceContinuation producers =
    trans
      (sym (continuedTraceIsIsotropicTrace producers))
      (continuedTraceIsLiteralR136Trace producers)

  asTerminalStressCovarianceMaxCut :
    LocalCWightmanTerminalProducers →
    Terminal.TerminalStressCovarianceMaxCut
      recovery selected directions
      (Hinge.LorentzianStressOperator hinge)
  asTerminalStressCovarianceMaxCut producers = record
    { Terminal.TerminalStressCovarianceMaxCut.selectedStressCovariance =
        asSelectedStressTensorBoostCovariance producers
    ; Terminal.TerminalStressCovarianceMaxCut.sameObjectEuclideanLorentzianTrace =
        sameObjectTraceContinuation producers
    }

  localCWightmanTerminalForcesVacuumEquationOfState :
    (producers : LocalCWightmanTerminalProducers) →
    Vacuum.pressure (lorentzianIsotropicStress producers)
    ≡ - Vacuum.rho (lorentzianIsotropicStress producers)
  localCWightmanTerminalForcesVacuumEquationOfState producers =
    Terminal.terminalMaxCutForcesVacuumEquationOfState
      recovery selected directions
      (asTerminalStressCovarianceMaxCut producers)

  localCWightmanTerminalPositiveRhoGivesNegativeActive :
    (producers : LocalCWightmanTerminalProducers) →
    0ℚ < Vacuum.rho (lorentzianIsotropicStress producers) →
    Vacuum.activeStress (lorentzianIsotropicStress producers) < 0ℚ
  localCWightmanTerminalPositiveRhoGivesNegativeActive producers positiveRho =
    Terminal.terminalMaxCutPositiveRhoGivesNegativeActive
      recovery selected directions
      (asTerminalStressCovarianceMaxCut producers)
      positiveRho

  selectedOperatorIsPinnedLocalCContinuationImage : Bool
  selectedOperatorIsPinnedLocalCContinuationImage = true

  producerASharedSelectedOperatorWithProducerB : Bool
  producerASharedSelectedOperatorWithProducerB = true

  remainingSharedHingeTheoremIsPhysical : Bool
  remainingSharedHingeTheoremIsPhysical = true
