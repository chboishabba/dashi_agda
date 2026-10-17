{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTerminalToStaticExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Static
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as VacuumRay

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

------------------------------------------------------------------------
-- TYPED LOCAL-C TERMINAL -> STATIC VACUUM PROMOTION
--
-- This is the strong version of the generic R136 reuse adapter.  The same-state
-- source is not represented by an arbitrary Set token: it is the actual
-- `PinnedLocalCTerminalProducers` package on the selected CMP119 Local-C object.
--
-- The remaining physical input is only the affine normalization-to-gravity
-- calibration plus a cosmological renormalization convention.
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
  where

  record PinnedLocalCStaticAffineCalibration
      (sourceNormalization : ℚ)
      (producers :
        Terminal.PinnedLocalCTerminalProducers
          recovery selected directions localC) : Set₁ where
    field
      normalizationToGravityScale : ℚ
      additiveGravityRenormalization : ℚ

      vacuumRhoUsesAffineCalibration :
        Vacuum.rho
          (Vacuum.stress
            (Terminal.pinnedLocalCVacuum
              recovery selected directions localC producers))
        ≡ normalizationToGravityScale * sourceNormalization
          + additiveGravityRenormalization

      CosmologicalRenormalizationCondition : Set
      cosmologicalRenormalizationCondition :
        CosmologicalRenormalizationCondition

  open PinnedLocalCStaticAffineCalibration public

  pinnedLocalCVacuumAmplitude :
    (producers :
      Terminal.PinnedLocalCTerminalProducers
        recovery selected directions localC) → ℚ
  pinnedLocalCVacuumAmplitude producers =
    Vacuum.rho
      (Vacuum.stress
        (Terminal.pinnedLocalCVacuum
          recovery selected directions localC producers))

  compilePinnedLocalCToStaticReceipt :
    ∀ {sourceNormalization}
      (producers :
        Terminal.PinnedLocalCTerminalProducers
          recovery selected directions localC) →
      PinnedLocalCStaticAffineCalibration sourceNormalization producers →
    Static.VacuumNormalizationToGravityReceipt sourceNormalization
  compilePinnedLocalCToStaticReceipt producers calibration = record
    { Static.VacuumNormalizationToGravityReceipt.renormalizedGravitationalAmplitude =
        pinnedLocalCVacuumAmplitude producers
    ; Static.VacuumNormalizationToGravityReceipt.physicalVacuumStress =
        VacuumRay.vacuumStressAt (pinnedLocalCVacuumAmplitude producers)
    ; Static.VacuumNormalizationToGravityReceipt.NormalizationToGravitySameObjectReceipt =
        Terminal.PinnedLocalCTerminalProducers
          recovery selected directions localC
    ; Static.VacuumNormalizationToGravityReceipt.normalizationToGravitySameObjectReceipt =
        producers
    ; Static.VacuumNormalizationToGravityReceipt.renormalizedEffectiveActionMetricResponse =
        VacuumRay.vacuumStressIsMinusLambdaMetric
          (pinnedLocalCVacuumAmplitude producers)
    ; Static.VacuumNormalizationToGravityReceipt.CosmologicalRenormalizationCondition =
        CosmologicalRenormalizationCondition calibration
    ; Static.VacuumNormalizationToGravityReceipt.cosmologicalRenormalizationCondition =
        cosmologicalRenormalizationCondition calibration
    ; Static.VacuumNormalizationToGravityReceipt.SameStateMetricVolumeReceipt =
        Terminal.PinnedLocalCTerminalProducers
          recovery selected directions localC
    ; Static.VacuumNormalizationToGravityReceipt.sameStateMetricVolumeReceipt =
        producers
    }

  compiledPinnedLocalCAmplitudeUsesAffineCalibration :
    ∀ {sourceNormalization}
      (producers :
        Terminal.PinnedLocalCTerminalProducers
          recovery selected directions localC)
      (calibration :
        PinnedLocalCStaticAffineCalibration sourceNormalization producers) →
    Static.renormalizedGravitationalAmplitude
      (compilePinnedLocalCToStaticReceipt producers calibration)
    ≡ normalizationToGravityScale calibration * sourceNormalization
      + additiveGravityRenormalization calibration
  compiledPinnedLocalCAmplitudeUsesAffineCalibration producers calibration =
    vacuumRhoUsesAffineCalibration calibration

  softR136SameStateTokenRequiredOnTypedRoute : Bool
  softR136SameStateTokenRequiredOnTypedRoute = false

  typedPinnedLocalCTerminalProducerRequired : Bool
  typedPinnedLocalCTerminalProducerRequired = true

  independentStaticMetricResponseTheoremRequiredAfterTypedTerminal : Bool
  independentStaticMetricResponseTheoremRequiredAfterTypedTerminal = false
