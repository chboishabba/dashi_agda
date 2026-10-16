{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanDirectStressGeometryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanTerminalToStaticExact as Prior
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact as Hinge
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.GRQFTSingleVacuumPositiveSourceNormalizedGeometryExact as Geometry

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

------------------------------------------------------------------------
-- DIRECT LOCAL-C/WIGHTMAN STRESS -> NORMALIZED STATIC GEOMETRY
--
-- The affine source-normalization -> rho map is required only when one wants to
-- use the scalar normalization coordinate as the gravitational source.  On the
-- preferred typed-stress route, the Local-C/Wightman terminal already owns the
-- SAME reconstructed vacuum stress and therefore its Lorentzian rho.
--
-- Conditional on rho>0, the existing positive-source normalized-geometry
-- compiler may consume that rho directly.  This does NOT choose the absolute
-- cosmological renormalization convention and does NOT identify the physical
-- stress*length^2 scale; those remain physical calibration payments.
------------------------------------------------------------------------

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
    (hinge : Hinge.LocalCWightmanStressHinge Y group localC)
  where

  localCWightmanVacuumRho :
    Terminal.LocalCWightmanTerminalProducers
      recovery selected directions localC hinge → ℚ
  localCWightmanVacuumRho producers =
    Vacuum.rho
      (Vacuum.stress
        (Terminal.localCWightmanVacuum
          recovery selected directions localC hinge producers))

  positiveLocalCWightmanRhoHasNormalizedStaticGeometry :
    (producers :
      Terminal.LocalCWightmanTerminalProducers
        recovery selected directions localC hinge) →
    0ℚ < localCWightmanVacuumRho producers →
    Geometry.PositiveSourceNormalizedStaticGeometry
      (localCWightmanVacuumRho producers)
  positiveLocalCWightmanRhoHasNormalizedStaticGeometry producers rhoPositive =
    Geometry.positiveSourceHasNormalizedStaticGeometry
      (localCWightmanVacuumRho producers) rhoPositive

  affineSourceNormalizationCalibrationRequiredForDirectStressRoute : Bool
  affineSourceNormalizationCalibrationRequiredForDirectStressRoute = false

  positiveTerminalRhoStillRequired : Bool
  positiveTerminalRhoStillRequired = true

  cosmologicalRenormalizationConventionStillPhysical : Bool
  cosmologicalRenormalizationConventionStillPhysical = true

  physicalStressLengthSquaredScaleStillExternal : Bool
  physicalStressLengthSquaredScaleStillExternal = true

  sourceNormalizationRouteStillAvailableWhenSourceCoordinateIsConsumer : Bool
  sourceNormalizationRouteStillAvailableWhenSourceCoordinateIsConsumer =
    Prior.affineNormalizationAndCosmologicalConventionStillRequired
