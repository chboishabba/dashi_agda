{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSTerminalCompilerExact where

------------------------------------------------------------------------
-- MARKED-STRESS OS HYPOTHESES -> TERMINAL COSMOLOGY MAX-CUT.
--
-- Standard imported mathematics:
--   Osterwalder--Schrader E->R reconstruction converts a Euclidean hierarchy
--   satisfying the OS hypotheses into a relativistic Wightman theory with
--   covariance, vacuum structure, locality and the corresponding analytic
--   continuation.
--
-- DASHI-specific mathematics:
--   prove that the EXISTING completed Local-C stress mark on the EXISTING
--   CMP119 same-family Schwinger hierarchy satisfies the marked OS hypotheses.
--
-- This compiler is specialized to the already-selected R136 four-direction
-- stress trace.  Therefore no independent Euclidean trace scalar appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSWightmanReconstructionExact as MarkedOS
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact as Hinge
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum

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

  record StandardMarkedStressOSTerminalAuthority
      (hypotheses :
        MarkedOS.LocalCStressMarkedOSHypotheses
          Y group lane localC)
      : Set₂ where
    field
      reconstructedHinge :
        Hinge.LocalCWightmanStressHinge
          Y group localC

      reconstructedTerminalConsequences :
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC reconstructedHinge

  open StandardMarkedStressOSTerminalAuthority public

  reconstructTerminalFromMarkedOS :
    (hypotheses :
      MarkedOS.LocalCStressMarkedOSHypotheses
        Y group lane localC) →
    StandardMarkedStressOSTerminalAuthority hypotheses →
    Σ (Hinge.LocalCWightmanStressHinge Y group localC)
      (λ hinge →
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC hinge)
  reconstructTerminalFromMarkedOS hypotheses authority =
    reconstructedHinge authority ,
    reconstructedTerminalConsequences authority

  markedOSHypothesesSufficeForTerminalVacuumBranch :
    (hypotheses :
      MarkedOS.LocalCStressMarkedOSHypotheses
        Y group lane localC) →
    StandardMarkedStressOSTerminalAuthority hypotheses →
    Set
  markedOSHypothesesSufficeForTerminalVacuumBranch hypotheses authority =
    let
      hinge = reconstructedHinge authority
      consequences = reconstructedTerminalConsequences authority
    in
    Terminal.LocalCWightmanTerminalProducers
      recovery selected directions localC hinge

  standardMarkedStressOSTerminalAuthorityLevel : ProofLevel
  standardMarkedStressOSTerminalAuthorityLevel = standardImported

  novelPhysicalFrontierIsMarkedLocalCOSHypotheses : Bool
  novelPhysicalFrontierIsMarkedLocalCOSHypotheses = true

  independentWightmanStressConstructionStillNeeded : Bool
  independentWightmanStressConstructionStillNeeded = false

  independentLorentzianTraceScalarStillNeeded : Bool
  independentLorentzianTraceScalarStillNeeded = false
