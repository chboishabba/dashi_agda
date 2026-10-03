{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyConcreteR109RealCompletionToR136Exact where

------------------------------------------------------------------------
-- B1 CONCRETE ENDPOINT COMPILER.
--
-- The older R136 sign route accepted an arbitrary rational finite sequence.
-- The live Pareto route now has the actual finite physical expectation
--
--   F_k(O) = finiteExpectation family k O
--
-- and a real completion estimate for the SAME R109 source.  This module wires
-- that concrete completion directly to the already-owned R130/R136 completed
-- four-diagonal response.  Thus no independent finite sequence and no extra
-- completed-value = R136 theorem remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as SignCompiler
import DASHI.Physics.Foundations.CMP119CosmologyR136CompletedFourDiagonalExpectationExact as Completed
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout

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
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
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
    {Configuration : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient : Quotient.RealQuotientConvergenceAuthority
      (RealLimit.Converges sequenceLimit)}
    {division : Division.RealDivisionAlgebra
      (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (source : R109.SourceNativeStressScaleCauchy)
    (observable : Configuration → ℝ)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (realOrder : SignCompiler.RealWeakStrictTransitivity)
    (reflection : Readout.NegativeOrderReflectionAtZero embedding)
  where

  module C = Concrete family source observable embedding

  concreteRealTailMarginForcesR136Negative :
    (anchor :
      C.ConcreteFiniteR109RealCompletion
        (Completed.completedFourDiagonalExpectation
          recovery selected directions)) →
    (start : Nat) →
    C.finiteR109Expectation start +ℝ C.embeddedR109Tail start <ℝ 0ℝ →
    Continuum.continuumFourDiagonalResponse recovery selected directions < 0ℚ
  concreteRealTailMarginForcesR136Negative anchor start marginNegative =
    subst
      (λ value → value < 0ℚ)
      (Completed.completedFourDiagonalExpectationIsR136Response
        recovery selected directions)
      (Readout.reflectNegative reflection
        (Completed.completedFourDiagonalExpectation
          recovery selected directions)
        (SignCompiler.weakThenStrict realOrder
          (C.completionUpperTail anchor start)
          marginNegative))

concreteRealCompletionToR136CompilerOwned : Bool
concreteRealCompletionToR136CompilerOwned = true

oldArbitraryRationalFiniteSequenceNeededForConcreteRoute : Bool
oldArbitraryRationalFiniteSequenceNeededForConcreteRoute = false

remainingB1PhysicalContentIsConcreteCompletionAndFiniteAttachment : Bool
remainingB1PhysicalContentIsConcreteCompletionAndFiniteAttachment = true

concreteRealCompletionToR136CompilerLevel : ProofLevel
concreteRealCompletionToR136CompilerLevel = machineChecked
