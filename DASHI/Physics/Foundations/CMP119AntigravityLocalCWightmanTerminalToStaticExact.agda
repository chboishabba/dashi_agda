{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanTerminalToStaticExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact as Hinge
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Static
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as VacuumRay

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
-- ONE LOCAL-C -> WIGHTMAN TERMINAL PACKAGE -> STATIC VACUUM PROMOTION
--
-- Master already owns a stronger terminal surface than the split pinned-Local-C
-- wrapper: `LocalCWightmanTerminalProducers` puts boost covariance and the
-- Euclidean->Lorentzian trace continuation on one selected continued stress
-- operator and one pinned reconstructed vacuum.
--
-- This adapter consumes that ONE physical package directly.  No independent
-- pinned boost/trace split, second static metric-response theorem, or second
-- continuation theorem is recharged.  The only remaining downstream physics is
-- the common affine source-normalization -> vacuum-density calibration and the
-- cosmological renormalization convention.
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

  record LocalCWightmanStaticAffineCalibration
      (sourceNormalization : ℚ)
      (producers :
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC hinge) : Set₁ where
    field
      normalizationToGravityScale : ℚ
      additiveGravityRenormalization : ℚ

      vacuumRhoUsesAffineCalibration :
        Vacuum.rho
          (Vacuum.stress
            (Terminal.localCWightmanVacuum
              recovery selected directions localC hinge producers))
        ≡ normalizationToGravityScale * sourceNormalization
          + additiveGravityRenormalization

      CosmologicalRenormalizationCondition : Set
      cosmologicalRenormalizationCondition :
        CosmologicalRenormalizationCondition

  open LocalCWightmanStaticAffineCalibration public

  localCWightmanVacuumAmplitude :
    (producers :
      Terminal.LocalCWightmanTerminalProducers
        recovery selected directions localC hinge) → ℚ
  localCWightmanVacuumAmplitude producers =
    Vacuum.rho
      (Vacuum.stress
        (Terminal.localCWightmanVacuum
          recovery selected directions localC hinge producers))

  compileLocalCWightmanTerminalToStaticReceipt :
    ∀ {sourceNormalization}
      (producers :
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC hinge) →
      LocalCWightmanStaticAffineCalibration sourceNormalization producers →
    Static.VacuumNormalizationToGravityReceipt sourceNormalization
  compileLocalCWightmanTerminalToStaticReceipt producers calibration = record
    { Static.VacuumNormalizationToGravityReceipt.renormalizedGravitationalAmplitude =
        localCWightmanVacuumAmplitude producers
    ; Static.VacuumNormalizationToGravityReceipt.physicalVacuumStress =
        VacuumRay.vacuumStressAt (localCWightmanVacuumAmplitude producers)
    ; Static.VacuumNormalizationToGravityReceipt.NormalizationToGravitySameObjectReceipt =
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC hinge
    ; Static.VacuumNormalizationToGravityReceipt.normalizationToGravitySameObjectReceipt =
        producers
    ; Static.VacuumNormalizationToGravityReceipt.renormalizedEffectiveActionMetricResponse =
        VacuumRay.vacuumStressIsMinusLambdaMetric
          (localCWightmanVacuumAmplitude producers)
    ; Static.VacuumNormalizationToGravityReceipt.CosmologicalRenormalizationCondition =
        CosmologicalRenormalizationCondition calibration
    ; Static.VacuumNormalizationToGravityReceipt.cosmologicalRenormalizationCondition =
        cosmologicalRenormalizationCondition calibration
    ; Static.VacuumNormalizationToGravityReceipt.SameStateMetricVolumeReceipt =
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC hinge
    ; Static.VacuumNormalizationToGravityReceipt.sameStateMetricVolumeReceipt =
        producers
    }

  compiledWightmanAmplitudeUsesAffineCalibration :
    ∀ {sourceNormalization}
      (producers :
        Terminal.LocalCWightmanTerminalProducers
          recovery selected directions localC hinge)
      (calibration :
        LocalCWightmanStaticAffineCalibration sourceNormalization producers) →
    Static.renormalizedGravitationalAmplitude
      (compileLocalCWightmanTerminalToStaticReceipt producers calibration)
    ≡ normalizationToGravityScale calibration * sourceNormalization
      + additiveGravityRenormalization calibration
  compiledWightmanAmplitudeUsesAffineCalibration producers calibration =
    vacuumRhoUsesAffineCalibration calibration

  selectedOperatorContinuationPackageAlreadyShared : Bool
  selectedOperatorContinuationPackageAlreadyShared = true

  independentPinnedBoostTraceSplitRequired : Bool
  independentPinnedBoostTraceSplitRequired = false

  independentStaticMetricResponseAfterWightmanTerminalRequired : Bool
  independentStaticMetricResponseAfterWightmanTerminalRequired = false

  affineNormalizationAndCosmologicalConventionStillRequired : Bool
  affineNormalizationAndCosmologicalConventionStillRequired = true
