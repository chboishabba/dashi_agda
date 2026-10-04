{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSSingleAuthorityExact where

------------------------------------------------------------------------
-- ONE STANDARD-IMPORTED MARKED OS AUTHORITY, ONE RECONSTRUCTED STRESS.
--
-- The older terminal authority could choose a reconstructed hinge independently
-- of the earlier OS/Wightman authority.  This owner removes that freedom.
-- Terminal covariance/trace consequences must be stated for exactly
--
--   reconstructLocalCWightmanStress hypotheses wightmanAuthority.
--
-- The analytic OS/Wightman theorem remains standardImported; no missing
-- distribution theory is fabricated inside DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSWightmanReconstructionExact as MarkedOS
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSTerminalCompilerExact as OldTerminal
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

  record StandardMarkedStressOSSingleAuthority
      (hypotheses : MarkedOS.LocalCStressMarkedOSHypotheses Y group lane localC)
      : Set₂ where
    field
      wightmanAuthority :
        MarkedOS.StandardMarkedStressOSWightmanAuthority hypotheses

      reconstructedTerminalConsequences :
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC
          (MarkedOS.reconstructLocalCWightmanStress hypotheses wightmanAuthority)

  open StandardMarkedStressOSSingleAuthority public

  asOldTerminalAuthority :
    (hypotheses : MarkedOS.LocalCStressMarkedOSHypotheses Y group lane localC) →
    StandardMarkedStressOSSingleAuthority hypotheses →
    OldTerminal.StandardMarkedStressOSTerminalAuthority
      recovery selected directions localC hypotheses
  asOldTerminalAuthority hypotheses authority = record
    { OldTerminal.StandardMarkedStressOSTerminalAuthority.reconstructedHinge =
        MarkedOS.reconstructLocalCWightmanStress
          hypotheses (wightmanAuthority authority)
    ; OldTerminal.StandardMarkedStressOSTerminalAuthority.reconstructedTerminalConsequences =
        reconstructedTerminalConsequences authority
    }

  terminalConsequencesAreForTheReconstructedStress :
    (hypotheses : MarkedOS.LocalCStressMarkedOSHypotheses Y group lane localC) →
    (authority : StandardMarkedStressOSSingleAuthority hypotheses) →
    Terminal.LocalCWightmanTerminalProducers
      recovery selected directions localC
      (MarkedOS.reconstructLocalCWightmanStress
        hypotheses (wightmanAuthority authority))
  terminalConsequencesAreForTheReconstructedStress hypotheses authority =
    reconstructedTerminalConsequences authority

  independentTerminalHingeChoiceEliminated : Bool
  independentTerminalHingeChoiceEliminated = true

  standardMarkedStressOSSingleAuthorityLevel : ProofLevel
  standardMarkedStressOSSingleAuthorityLevel = standardImported
