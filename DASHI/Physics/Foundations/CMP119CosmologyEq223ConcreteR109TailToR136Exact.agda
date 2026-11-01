{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteR109TailToR136Exact where

------------------------------------------------------------------------
-- PREFERRED EQ.(2.23) -> R136 ROUTE ON THE ACTUAL FINITE R109 FAMILY.
--
-- This is the concrete replacement for the older preferred consumer that
-- carried an arbitrary rational `Nat -> Q` finite endpoint sequence.
--
-- At one selected cutoff k the only finite same-object datum is now
--
--   finiteExpectation pinnedFamily k selectedObservable
--     = embed (D_Gamma,k^Weyl).
--
-- The completion datum is likewise on that same concrete real sequence:
--
--   embed Q_R136 <= F_k + embed Tail_R109(k).
--
-- The already-proved Eq.(2.23) estimate
--
--   D_Gamma,k^Weyl <= M_ERB + c_V
--
-- and strict rational source margin
--
--   (M_ERB + c_V) + Tail_R109(k) < 0
--
-- therefore compile to Q_R136 < 0 without any arbitrary endpoint sequence and
-- without an exact finite-cutoff = continuum equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologyConcreteR109RealCompletionToR136Exact as ConcreteR136
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223FiniteEffectiveActionUpperExact as Finite
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136CompletedFourDiagonalExpectationExact as Completed
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
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
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

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
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient : Quotient.RealQuotientConvergenceAuthority
      (RealLimit.Converges sequenceLimit)}
    {division : Division.RealDivisionAlgebra
      (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (observable : Configuration → ℝ)
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
    (realOrder : RealSign.RealWeakStrictTransitivity)
    (reflection :
      Readout.NegativeOrderReflectionAtZero (Additive.base embedding))
  where

  module F =
    Finite sourceVariation measure orderLaws partition scaleLaw signLaws referenceFixed
  module E = Envelope sourceVariation measure orderLaws partition scaleLaw
  module C = Concrete family r109Source observable (Additive.base embedding)
  module R = ConcreteR136 recovery selected directions family r109Source observable
    (Additive.base embedding) realOrder reflection

  record ConcreteFiniteR109ScaleAnchor (start : Nat) : Set₁ where
    field
      completion :
        C.ConcreteFiniteR109RealCompletion
          (Completed.completedFourDiagonalExpectation
            recovery selected directions)

      finiteExpectationIsSelectedDGamma :
        C.finiteR109Expectation start
        ≡ Embed.embed (Additive.base embedding) F.finiteEffectiveActionWeyl

  open ConcreteFiniteR109ScaleAnchor public

  finiteDGammaBelowCombinedSourceUpper :
    (envelope : E.CombinedERBTraceEnvelope) →
    F.finiteEffectiveActionWeyl
    ≤ E.combinedUpper envelope
      + Eq223.eq223VacuumTraceCoefficient sourceVariation
  finiteDGammaBelowCombinedSourceUpper envelope =
    F.finiteEffectiveActionWeylBelowCombinedSourceUpper envelope

  combinedSourcePlusTailMarginForcesNegativeR136Concrete :
    (start : Nat)
    (anchor : ConcreteFiniteR109ScaleAnchor start)
    (envelope : E.CombinedERBTraceEnvelope) →
    (E.combinedUpper envelope
      + Eq223.eq223VacuumTraceCoefficient sourceVariation)
      + Tail.r109RemainingTail r109Source start
      < 0ℚ →
    Continuum.continuumFourDiagonalResponse recovery selected directions < 0ℚ
  combinedSourcePlusTailMarginForcesNegativeR136Concrete
      start anchor envelope sourceTailMargin =
    let
      finitePlusTailBelowSourcePlusTail :
        F.finiteEffectiveActionWeyl
          + Tail.r109RemainingTail r109Source start
        ≤
        (E.combinedUpper envelope
          + Eq223.eq223VacuumTraceCoefficient sourceVariation)
          + Tail.r109RemainingTail r109Source start
      finitePlusTailBelowSourcePlusTail =
        ℚP.+-mono-≤
          (finiteDGammaBelowCombinedSourceUpper envelope)
          ℚP.≤-refl

      finitePlusTailNegative :
        F.finiteEffectiveActionWeyl
          + Tail.r109RemainingTail r109Source start
        < 0ℚ
      finitePlusTailNegative =
        ℚP.≤-<-trans finitePlusTailBelowSourcePlusTail sourceTailMargin

      embeddedFinitePlusTailNegative :
        Embed.embed (Additive.base embedding)
          (F.finiteEffectiveActionWeyl
            + Tail.r109RemainingTail r109Source start)
        <ℝ 0ℝ
      embeddedFinitePlusTailNegative =
        subst
          (λ right →
            Embed.embed (Additive.base embedding)
              (F.finiteEffectiveActionWeyl
                + Tail.r109RemainingTail r109Source start)
            <ℝ right)
          (Embed.zeroExact (Additive.base embedding))
          (Embed.strictOrderPreserving
            (Additive.base embedding) finitePlusTailNegative)

      selectedFinitePlusTailNegative :
        C.finiteR109Expectation start +ℝ C.embeddedR109Tail start <ℝ 0ℝ
      selectedFinitePlusTailNegative =
        subst
          (λ left → left +ℝ C.embeddedR109Tail start <ℝ 0ℝ)
          (sym (finiteExpectationIsSelectedDGamma anchor))
          (subst
            (λ left → left <ℝ 0ℝ)
            (Additive.addExact embedding
              F.finiteEffectiveActionWeyl
              (Tail.r109RemainingTail r109Source start))
            embeddedFinitePlusTailNegative)
    in
    R.concreteRealTailMarginForcesR136Negative
      (completion anchor) start selectedFinitePlusTailNegative

preferredConcreteTailRouteEliminatesArbitraryFiniteSequence : Bool
preferredConcreteTailRouteEliminatesArbitraryFiniteSequence = true

preferredConcreteTailRouteNeedsFiniteEqualsContinuum : Bool
preferredConcreteTailRouteNeedsFiniteEqualsContinuum = false

remainingB1FiniteSameObjectLeafIsPinnedExpectationEqualsDGamma : Bool
remainingB1FiniteSameObjectLeafIsPinnedExpectationEqualsDGamma = true

remainingB1CompletionLeafIsConcreteSameSequenceTailBound : Bool
remainingB1CompletionLeafIsConcreteSameSequenceTailBound = true

preferredConcreteEq223R109TailCompilerLevel : ProofLevel
preferredConcreteEq223R109TailCompilerLevel = machineChecked
