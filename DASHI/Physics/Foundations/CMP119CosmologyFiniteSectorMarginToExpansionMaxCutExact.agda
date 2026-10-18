{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiniteSectorMarginToExpansionMaxCutExact where

------------------------------------------------------------------------
-- END-TO-END FINITE SECTOR ROUTE (conditional only on the live producer leaves).
--
--   N_nonW/Z + R109-tail < 0
--     + finite D_Gamma is the selected absolute stress expectation
--     + marked-OS reconstruction root
--   --------------------------------------------------------------
--     positive matter acceleration contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyR144AbsoluteExpectationToR136Exact as Absolute
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyNormalizedSectorWeylResponseExact as Normalized
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal

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
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
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
    (sourceCauchy : R109.SourceNativeStressScaleCauchy)
    {G X LocalConfiguration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume RootType ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X LocalConfiguration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume RootType ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
  where

  literalTrace : ℚ
  literalTrace = Root.literalContinuumTrace recovery selected directions localC

  continuumResponse : ℚ
  continuumResponse =
    Continuum.continuumFourDiagonalResponse recovery selected directions

  continuumNegativeGivesLiteralNegative :
    continuumResponse < 0ℚ →
    literalTrace < 0ℚ
  continuumNegativeGivesLiteralNegative responseNegative =
    subst
      (λ value → value < 0ℚ)
      (Continuum.continuumFourDiagonalResponseIsLiteralStressPairing
        recovery selected directions)
      responseNegative

  finiteSectorMarginForcesPositiveMatterAcceleration :
    ∀ {FiniteConfiguration}
      (measure : Physical.PhysicalFiniteYMMeasure FiniteConfiguration ℚ)
      (d : Source.CompleteFiniteMetricVariation FiniteConfiguration)
      (laws : Sign.RationalWeylSignIntegrationLaws measure)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      (referenceFixed :
        ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
      (absolute :
        Absolute.AbsoluteFiniteExpectationAnchor
          recovery selected directions sourceCauchy)
      (scale : Nat)
      (finiteExpectationIsGamma :
        Absolute.finiteExpectation absolute scale
        ≡ Convention.matterEffectiveActionWeylResponse measure partition d)
      (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC)
      (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    Normalized.normalizedNonWilsonWeylNumerator measure partition d
      + Tail.r109RemainingTail sourceCauchy scale < 0ℚ →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  finiteSectorMarginForcesPositiveMatterAcceleration
      measure d laws partition referenceFixed absolute scale
      finiteExpectationIsGamma root positiveGravityFactor
      factorPositive normalizedMargin =
    let
      gammaMargin :
        Convention.matterEffectiveActionWeylResponse measure partition d
          + Tail.r109RemainingTail sourceCauchy scale < 0ℚ
      gammaMargin =
        Normalized.normalizedSectorMarginForcesFiniteGammaNegative
          measure d laws partition referenceFixed
          (Tail.r109RemainingTail sourceCauchy scale)
          normalizedMargin

      finiteMargin :
        Absolute.finiteExpectation absolute scale
          + Tail.r109RemainingTail sourceCauchy scale < 0ℚ
      finiteMargin =
        subst
          (λ value →
            value + Tail.r109RemainingTail sourceCauchy scale < 0ℚ)
          (sym finiteExpectationIsGamma)
          gammaMargin

      r136Negative : continuumResponse < 0ℚ
      r136Negative =
        Absolute.finiteTailMarginForcesR136Negative
          recovery selected directions sourceCauchy
          absolute scale finiteMargin
    in
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (continuumNegativeGivesLiteralNegative r136Negative)

finiteSectorRouteNowCompilesToMatterAcceleration : Bool
finiteSectorRouteNowCompilesToMatterAcceleration = true

remainingFiniteSectorLeavesAreAbsoluteAnchorMarginAndMarkedOS : Bool
remainingFiniteSectorLeavesAreAbsoluteAnchorMarginAndMarkedOS = true
