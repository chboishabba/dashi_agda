{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact where

------------------------------------------------------------------------
-- ROOT MAX-CUT:
--
--   existing R109/R128/Local-C data
--   + two exact semantic/topology bridges
--   + three new marked analytic conditions (E1/E2/E4)
--   + standard OS marked-field reconstruction authority
--
--       ==> one Local-C -> Wightman stress hinge
--       ==> boost covariance + vacuum invariance + trace continuation
--       ==> p = -rho
--       ==> rho > 0 -> rho + 3p < 0.
--
-- The root does not accept any independently chosen Lorentzian stress,
-- reconstructed vacuum, or Euclidean trace scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_; -_)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSHypothesisMaxCutExact as HypCut
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSWightmanReconstructionExact as MarkedOS
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSTerminalCompilerExact as OSTerminal
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact as Hinge
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
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

  record MarkedStressOSMaxCutRoot : Set₂ where
    field
      hypothesisCut :
        HypCut.MarkedStressOSHypothesisMaxCut
          Y group lane localC

      standardAuthority :
        OSTerminal.StandardMarkedStressOSTerminalAuthority
          recovery selected directions localC
          (HypCut.compileMarkedOSHypotheses hypothesisCut)

  open MarkedStressOSMaxCutRoot public

  markedOSHypotheses :
    MarkedStressOSMaxCutRoot →
    MarkedOS.LocalCStressMarkedOSHypotheses
      Y group lane localC
  markedOSHypotheses root =
    HypCut.compileMarkedOSHypotheses (hypothesisCut root)

  reconstructedHinge :
    MarkedStressOSMaxCutRoot →
    Hinge.LocalCWightmanStressHinge
      Y group localC
  reconstructedHinge root =
    OSTerminal.reconstructedHinge (standardAuthority root)

  reconstructedTerminalConsequences :
    (root : MarkedStressOSMaxCutRoot) →
    Terminal.LocalCWightmanTerminalProducers
      recovery selected directions localC
      (reconstructedHinge root)
  reconstructedTerminalConsequences root =
    OSTerminal.reconstructedTerminalConsequences
      (standardAuthority root)

  rootForcesVacuumEquationOfState :
    (root : MarkedStressOSMaxCutRoot) →
    Vacuum.pressure
      (Terminal.lorentzianIsotropicStress
        (reconstructedTerminalConsequences root))
    ≡
    - Vacuum.rho
      (Terminal.lorentzianIsotropicStress
        (reconstructedTerminalConsequences root))
  rootForcesVacuumEquationOfState root =
    Terminal.localCWightmanTerminalForcesVacuumEquationOfState
      recovery selected directions localC
      (reconstructedHinge root)
      (reconstructedTerminalConsequences root)

  rootPositiveRhoGivesNegativeActive :
    (root : MarkedStressOSMaxCutRoot) →
    0ℚ <
      Vacuum.rho
        (Terminal.lorentzianIsotropicStress
          (reconstructedTerminalConsequences root)) →
    Vacuum.activeStress
      (Terminal.lorentzianIsotropicStress
        (reconstructedTerminalConsequences root))
    < 0ℚ
  rootPositiveRhoGivesNegativeActive root positiveRho =
    Terminal.localCWightmanTerminalPositiveRhoGivesNegativeActive
      recovery selected directions localC
      (reconstructedHinge root)
      (reconstructedTerminalConsequences root)
      positiveRho

  remainingNovelMarkedAnalyticCoreCount : Nat
  remainingNovelMarkedAnalyticCoreCount = 3

  remainingSemanticTopologyBridgeCount : Nat
  remainingSemanticTopologyBridgeCount = 2

  noIndependentLorentzianStressChoice : Bool
  noIndependentLorentzianStressChoice = true

  noIndependentTraceChoice : Bool
  noIndependentTraceChoice = true
