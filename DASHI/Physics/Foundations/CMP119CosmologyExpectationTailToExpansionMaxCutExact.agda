{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyExpectationTailToExpansionMaxCutExact where

------------------------------------------------------------------------
-- COMPOSE PRODUCER B WITH THE ALREADY-COMPILED MARKED-OS CONSUMER.
--
-- Once the absolute completed stress expectation is identified with the root's
-- literal R136 four-direction trace, the explicit R109 tail theorem gives:
--
--   finiteExpectation_k + remainingTail_k < 0
--       ==> literal R136 trace < 0
--       ==> Lorentzian active stress < 0
--       ==> positive matter acceleration contribution (for positive G-factor).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Completion
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
     Scale Volume RootType ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
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

  record ExpectationCompletionToR136Trace
      (source : R109.SourceNativeStressScaleCauchy)
      (anchor : Completion.R144R109AbsoluteExpectationCompletion source)
      : Set₁ where
    field
      completedExpectationIsLiteralR136Trace :
        Completion.completedExpectation anchor
        ≡ Root.literalContinuumTrace recovery selected directions localC

  open ExpectationCompletionToR136Trace public

  finiteTailMarginForcesLiteralR136TraceNegative :
    ∀ {source : R109.SourceNativeStressScaleCauchy}
      {anchor : Completion.R144R109AbsoluteExpectationCompletion source} →
    ExpectationCompletionToR136Trace source anchor →
    (start : Nat) →
    Completion.finiteExpectation anchor start
      + Completion.r109RemainingTail source start < 0ℚ →
    Root.literalContinuumTrace recovery selected directions localC < 0ℚ
  finiteTailMarginForcesLiteralR136TraceNegative
      {anchor = anchor} bridge start marginNegative =
    subst
      (λ value → value < 0ℚ)
      (completedExpectationIsLiteralR136Trace bridge)
      (Completion.negativeFiniteMarginForcesNegativeCompletion
        anchor start marginNegative)

  finiteTailMarginForcesPositiveMatterAcceleration :
    ∀ {source : R109.SourceNativeStressScaleCauchy}
      {anchor : Completion.R144R109AbsoluteExpectationCompletion source} →
    (bridge : ExpectationCompletionToR136Trace source anchor) →
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC) →
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    (start : Nat) →
    Completion.finiteExpectation anchor start
      + Completion.r109RemainingTail source start < 0ℚ →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  finiteTailMarginForcesPositiveMatterAcceleration
      bridge root positiveGravityFactor factorPositive start marginNegative =
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (finiteTailMarginForcesLiteralR136TraceNegative
        bridge start marginNegative)

finiteTailMarginNowFeedsCompiledExpansionConsumer : Bool
finiteTailMarginNowFeedsCompiledExpansionConsumer = true

remainingBLeafIsCompletedExpectationIdentity : Bool
remainingBLeafIsCompletedExpectationIdentity = true
