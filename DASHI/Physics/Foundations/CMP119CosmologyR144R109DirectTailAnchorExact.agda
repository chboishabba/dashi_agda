{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact where

------------------------------------------------------------------------
-- B1 DIRECT-TAIL MAX-CUT.
--
-- The concrete preferred route currently carries two physical fields at a
-- selected cutoff k:
--
--   F_k = embed(D_Gamma,k),
--   embed(Q_R136) <= F_k + embed(Tail_R109(k)).
--
-- Downstream sign transport uses only their composition.  Therefore the
-- terminal B1 source theorem can be stated as ONE direct same-object inequality
--
--   embed(Q_R136)
--     <= embed(D_Gamma,k) + embed(Tail_R109(k)).
--
-- This file proves the current two-field concrete anchor compiles to that one
-- inequality and proves that the one inequality alone is sufficient for the
-- rational sign consumer.  No signed Round109 telescope is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

module _
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
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
  where

  baseEmbedding = Additive.base embedding
  module C = Concrete family source observable baseEmbedding

  record DirectR144R109TailAnchor
      (completedRationalResponse finiteRationalDGamma : ℚ)
      (start : Nat) : Set₁ where
    field
      completionBelowFinitePlusTail :
        Embed.embed baseEmbedding completedRationalResponse
        ≤ℝ
        Embed.embed baseEmbedding finiteRationalDGamma
          +ℝ C.embeddedR109Tail start

  open DirectR144R109TailAnchor public

  fromConcreteCompletionAndFiniteIdentity :
    ∀ {completed finite start} →
    C.ConcreteFiniteR109RealCompletion completed →
    C.finiteR109Expectation start
      ≡ Embed.embed baseEmbedding finite →
    DirectR144R109TailAnchor completed finite start
  fromConcreteCompletionAndFiniteIdentity
      {completed} {finite} {start} completion finiteExact = record
    { DirectR144R109TailAnchor.completionBelowFinitePlusTail =
        subst
          (λ finiteValue →
            Embed.embed baseEmbedding completed
            ≤ℝ finiteValue +ℝ C.embeddedR109Tail start)
          finiteExact
          (C.completionUpperTail completion start)
    }

  directTailMarginForcesNegativeRationalCompletion :
    (realOrder : RealSign.RealWeakStrictTransitivity) →
    (reflection : Readout.NegativeOrderReflectionAtZero baseEmbedding) →
    ∀ {completed finite start} →
    DirectR144R109TailAnchor completed finite start →
    finite + Tail.r109RemainingTail source start < 0ℚ →
    completed < 0ℚ
  directTailMarginForcesNegativeRationalCompletion
      realOrder reflection {completed} {finite} {start} anchor rationalMargin =
    let
      tail = Tail.r109RemainingTail source start

      embeddedSumNegative :
        Embed.embed baseEmbedding (finite + tail) <ℝ 0ℝ
      embeddedSumNegative =
        subst
          (λ right → Embed.embed baseEmbedding (finite + tail) <ℝ right)
          (Embed.zeroExact baseEmbedding)
          (Embed.strictOrderPreserving baseEmbedding rationalMargin)

      finitePlusTailNegative :
        Embed.embed baseEmbedding finite
          +ℝ Embed.embed baseEmbedding tail <ℝ 0ℝ
      finitePlusTailNegative =
        subst
          (λ left → left <ℝ 0ℝ)
          (Additive.addExact embedding finite tail)
          embeddedSumNegative

      completedEmbeddedNegative :
        Embed.embed baseEmbedding completed <ℝ 0ℝ
      completedEmbeddedNegative =
        RealSign.weakThenStrict realOrder
          (completionBelowFinitePlusTail anchor)
          finitePlusTailNegative
    in
    Readout.reflectNegative reflection completed completedEmbeddedNegative

preferredB1CompressedToOneDirectTailInequality : Bool
preferredB1CompressedToOneDirectTailInequality = true

directTailAnchorNeedsNoSignedDifferenceIdentity : Bool
directTailAnchorNeedsNoSignedDifferenceIdentity = true

directTailAnchorNeedsNoSeparateEndpointEquality : Bool
directTailAnchorNeedsNoSeparateEndpointEquality = true

currentConcreteTwoFieldAnchorCompilesToDirectAnchor : Bool
currentConcreteTwoFieldAnchorCompilesToDirectAnchor = true
