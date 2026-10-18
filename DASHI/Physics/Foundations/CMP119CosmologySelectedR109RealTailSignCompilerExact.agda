{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact where

------------------------------------------------------------------------
-- SELECTED FINITE R109 REAL COMPLETION -> RATIONAL SIGN.
--
-- The concrete B1 owner now evaluates the SAME selected stress observable on
-- the literal pinned finite physical family.  Its completion inequality lives
-- in the repository's abstract real carrier:
--
--   embed Q∞ <= F_k + embed Tail_k.
--
-- This file removes the remaining representation-only sign seam.  Given the
-- standard mixed weak/strict order transitivity of R and the existing ordered
-- rational embedding, a negative real tail margin forces Q∞ < 0.  With the
-- already-existing additive Q->R embedding, a rational finite response
-- identity
--
--   F_k = embed q_k
--
-- reduces the whole sign check to the exact rational inequality
--
--   q_k + Tail_k < 0.
--
-- No finite-cutoff = continuum equality and no new physics assumption appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RealWeakStrictTransitivity : Set₁ where
  field
    weakThenStrict :
      ∀ {left middle right : ℝ} →
      left ≤ℝ middle →
      middle <ℝ right →
      left <ℝ right

open RealWeakStrictTransitivity public

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
    (realOrder : RealWeakStrictTransitivity)
    (reflection :
      Readout.NegativeOrderReflectionAtZero
        (Additive.base embedding))
  where

  module C = Concrete family source observable (Additive.base embedding)

  realTailMarginForcesNegativeRationalCompletion :
    (completedRationalExpectation : ℚ) →
    C.ConcreteFiniteR109RealCompletion completedRationalExpectation →
    (start : Nat) →
    C.finiteR109Expectation start +ℝ C.embeddedR109Tail start <ℝ 0ℝ →
    completedRationalExpectation < 0ℚ
  realTailMarginForcesNegativeRationalCompletion
      completed anchor start marginNegative =
    Readout.reflectNegative reflection completed
      (weakThenStrict realOrder
        (C.completionUpperTail anchor start)
        marginNegative)

  rationalFiniteTailMarginForcesNegativeCompletion :
    (completedRationalExpectation finiteRationalExpectation : ℚ) →
    C.ConcreteFiniteR109RealCompletion completedRationalExpectation →
    (start : Nat) →
    C.finiteR109Expectation start
      ≡ Embed.embed (Additive.base embedding) finiteRationalExpectation →
    finiteRationalExpectation + Tail.r109RemainingTail source start < 0ℚ →
    completedRationalExpectation < 0ℚ
  rationalFiniteTailMarginForcesNegativeCompletion
      completed finite anchor start finiteExact rationalMargin =
    let
      baseEmbedding = Additive.base embedding
      tail = Tail.r109RemainingTail source start

      completionBelowEmbeddedSum :
        Embed.embed baseEmbedding completed
        ≤ℝ Embed.embed baseEmbedding (finite + tail)
      completionBelowEmbeddedSum =
        subst
          (λ right → Embed.embed baseEmbedding completed ≤ℝ right)
          (sym (Additive.addExact embedding finite tail))
          (subst
            (λ finiteValue →
              Embed.embed baseEmbedding completed
              ≤ℝ finiteValue +ℝ Embed.embed baseEmbedding tail)
            finiteExact
            (C.completionUpperTail anchor start))

      embeddedSumNegative :
        Embed.embed baseEmbedding (finite + tail) <ℝ 0ℝ
      embeddedSumNegative =
        subst
          (λ right → Embed.embed baseEmbedding (finite + tail) <ℝ right)
          (Embed.zeroExact baseEmbedding)
          (Embed.strictOrderPreserving baseEmbedding rationalMargin)

      completedEmbeddedNegative :
        Embed.embed baseEmbedding completed <ℝ 0ℝ
      completedEmbeddedNegative =
        weakThenStrict realOrder
          completionBelowEmbeddedSum embeddedSumNegative
    in
    Readout.reflectNegative reflection completed completedEmbeddedNegative

realCompletionTailSignCompilerOwned : Bool
realCompletionTailSignCompilerOwned = true

additiveEmbeddingAlreadyRepositoryOwned : Bool
additiveEmbeddingAlreadyRepositoryOwned = true

remainingPhysicalB1DatumIsFiniteR144EqualsPinnedR109Expectation : Bool
remainingPhysicalB1DatumIsFiniteR144EqualsPinnedR109Expectation = true

selectedR109RealTailSignCompilerLevel : ProofLevel
selectedR109RealTailSignCompilerLevel = machineChecked

realWeakStrictTransitivityLevel : ProofLevel
realWeakStrictTransitivityLevel = standardImported
