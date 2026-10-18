{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyDirectSourceNumeratorTailToExpansionExact where

------------------------------------------------------------------------
-- FINAL PREFERRED B1+B2 CONSUMER.
--
-- The terminal source-facing premises are now exactly:
--
--   B1  embed(Q_R136) <= embed(DGamma_k) + embed(Tail_109(k))
--
--   B2  N_k + Tail_109(k) * Z_k < 0
--
-- where N_k and Z_k are the literal unnormalized finite source numerator and
-- positive partition function.  The existing quotient theorem converts B2 to
-- DGamma_k + Tail_109(k) < 0; the direct B1 anchor then forces the canonical
-- completed R136 four-diagonal response negative; the existing marked-OS /
-- Local-C terminal consumer turns that exact sign into positive matter
-- acceleration for a positive gravity factor.
--
-- No E/R/B envelope, vacuum coefficient threshold, arbitrary finite sequence,
-- independently chosen observable, or finite=continuum equality is introduced
-- at this terminal sign cut.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyDirectTailFromSourceNumeratorExact as DirectNumerator
import DASHI.Physics.Foundations.CMP119CosmologyUnnormalizedSourceTailMarginExact as Margin
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136CompletedFourDiagonalExpectationExact as Completed
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as VacuumFactor
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
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
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

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
    (r109Source : R109.SourceNativeStressScaleCauchy)
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
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {sourceScale : Nat}
    (sourceVariation :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration sourceScale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : VacuumFactor.RationalHaarScaleLaw measure)
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation sourceVariation) h x
      ≡ 0ℚ)
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
    (realOrder : RealSign.RealWeakStrictTransitivity)
    (reflection :
      Readout.NegativeOrderReflectionAtZero (Additive.base embedding))
  where

  module M =
    Margin sourceVariation measure orderLaws partition scaleLaw signLaws referenceFixed

  module D =
    DirectNumerator sourceVariation measure orderLaws partition scaleLaw signLaws
      referenceFixed r109Source embedding realOrder reflection

  completedResponse : ℚ
  completedResponse =
    Completed.completedFourDiagonalExpectation recovery selected directions

  directSourceNumeratorTailMarginForcesNegativeR136 :
    (start : Nat)
    (anchor :
      Direct.DirectR144R109TailAnchor
        embedding r109Source completedResponse
        M.F.finiteEffectiveActionWeyl start) →
    M.F.nonWilsonNumerator
      + Tail.r109RemainingTail r109Source start * M.F.z
      < 0ℚ →
    Continuum.continuumFourDiagonalResponse recovery selected directions < 0ℚ
  directSourceNumeratorTailMarginForcesNegativeR136 start anchor sourceMargin =
    subst
      (λ value → value < 0ℚ)
      (Completed.completedFourDiagonalExpectationIsR136Response
        recovery selected directions)
      (D.sourceNumeratorMarginForcesNegativeCompletion anchor sourceMargin)

  directSourceNumeratorTailMarginForcesPositiveMatterAcceleration :
    (start : Nat)
    (anchor :
      Direct.DirectR144R109TailAnchor
        embedding r109Source completedResponse
        M.F.finiteEffectiveActionWeyl start)
    (sourceMargin :
      M.F.nonWilsonNumerator
        + Tail.r109RemainingTail r109Source start * M.F.z
        < 0ℚ)
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC)
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  directSourceNumeratorTailMarginForcesPositiveMatterAcceleration
      start anchor sourceMargin root positiveGravityFactor factorPositive =
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (directSourceNumeratorTailMarginForcesNegativeR136
        start anchor sourceMargin)

directSourceNumeratorTailMarginCompilesToMatterAcceleration : Bool
directSourceNumeratorTailMarginCompilesToMatterAcceleration = true

directSourceNumeratorRouteNeedsCombinedERBEnvelope : Bool
directSourceNumeratorRouteNeedsCombinedERBEnvelope = false

directSourceNumeratorRouteNeedsVacuumThreshold : Bool
directSourceNumeratorRouteNeedsVacuumThreshold = false

directSourceNumeratorRouteNeedsFiniteFamilyOrObservable : Bool
directSourceNumeratorRouteNeedsFiniteFamilyOrObservable = false

directSourceNumeratorRouteNeedsFiniteEqualsContinuum : Bool
directSourceNumeratorRouteNeedsFiniteEqualsContinuum = false
