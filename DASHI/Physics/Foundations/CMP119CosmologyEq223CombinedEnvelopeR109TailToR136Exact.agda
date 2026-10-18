{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedEnvelopeR109TailToR136Exact where

------------------------------------------------------------------------
-- PREFERRED FINITE -> CONTINUUM SIGN ROUTE WITHOUT FINITE=CONTINUUM EQUALITY.
--
-- The selected finite Eq.(2.23) source gives
--
--   D_Gamma,k^Weyl <= M_ERB + c_V.
--
-- Round109 gives an explicit remaining tail to the completed stress response,
-- and Round130/R136 identify that completion with the literal R136 response.
-- Therefore it is enough to identify ONE finite scale value with the R109
-- finite expectation sequence and prove
--
--   (M_ERB + c_V) + Tail_R109(k) < 0.
--
-- No exact equality between a finite-cutoff response and the continuum R136
-- response is assumed or required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223FiniteEffectiveActionUpperExact as Finite
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR144AbsoluteExpectationToR136Exact as Absolute
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order

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
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation sourceVariation) h x
      ≡ 0ℚ)
  where

  module F =
    Finite sourceVariation measure orderLaws partition scaleLaw signLaws referenceFixed
  module E = Envelope sourceVariation measure orderLaws partition scaleLaw
  module A = Absolute recovery selected directions r109Source

  record FiniteR109ScaleAnchor
      (absolute : A.AbsoluteFiniteExpectationAnchor)
      (start : Nat) : Set where
    field
      finiteExpectationIsSelectedDGamma :
        A.finiteExpectation absolute start
        ≡ F.finiteEffectiveActionWeyl

  open FiniteR109ScaleAnchor public

  finiteExpectationBelowCombinedSourceUpper :
    (absolute : A.AbsoluteFiniteExpectationAnchor)
    (start : Nat)
    (anchor : FiniteR109ScaleAnchor absolute start)
    (envelope : E.CombinedERBTraceEnvelope) →
    A.finiteExpectation absolute start
    ≤ E.combinedUpper envelope
      + Eq223.eq223VacuumTraceCoefficient sourceVariation
  finiteExpectationBelowCombinedSourceUpper absolute start anchor envelope =
    subst
      (λ value →
        value
        ≤ E.combinedUpper envelope
          + Eq223.eq223VacuumTraceCoefficient sourceVariation)
      (sym (finiteExpectationIsSelectedDGamma anchor))
      (F.finiteEffectiveActionWeylBelowCombinedSourceUpper envelope)

  combinedSourcePlusTailMarginForcesNegativeR136 :
    (absolute : A.AbsoluteFiniteExpectationAnchor)
    (start : Nat)
    (anchor : FiniteR109ScaleAnchor absolute start)
    (envelope : E.CombinedERBTraceEnvelope) →
    (E.combinedUpper envelope
      + Eq223.eq223VacuumTraceCoefficient sourceVariation)
      + Tail.r109RemainingTail r109Source start
      < 0ℚ →
    Continuum.continuumFourDiagonalResponse recovery selected directions < 0ℚ
  combinedSourcePlusTailMarginForcesNegativeR136
      absolute start anchor envelope sourceTailMargin =
    let
      finitePlusTailBelowSourcePlusTail :
        A.finiteExpectation absolute start
          + Tail.r109RemainingTail r109Source start
        ≤
        (E.combinedUpper envelope
          + Eq223.eq223VacuumTraceCoefficient sourceVariation)
          + Tail.r109RemainingTail r109Source start
      finitePlusTailBelowSourcePlusTail =
        ℚP.+-mono-≤
          (finiteExpectationBelowCombinedSourceUpper
            absolute start anchor envelope)
          ℚP.≤-refl

      finitePlusTailNegative :
        A.finiteExpectation absolute start
          + Tail.r109RemainingTail r109Source start
        < 0ℚ
      finitePlusTailNegative =
        ℚP.≤-<-trans
          finitePlusTailBelowSourcePlusTail
          sourceTailMargin
    in
    A.finiteTailMarginForcesR136Negative
      absolute start finitePlusTailNegative

  exactFiniteEqualsContinuumWeldNotRequired : Bool
  exactFiniteEqualsContinuumWeldNotRequired = true

  preferredContinuumSignUsesExplicitR109Tail : Bool
  preferredContinuumSignUsesExplicitR109Tail = true

  remainingSameSequenceLeafIsFiniteR109ScaleAnchor : Bool
  remainingSameSequenceLeafIsFiniteR109ScaleAnchor = true
