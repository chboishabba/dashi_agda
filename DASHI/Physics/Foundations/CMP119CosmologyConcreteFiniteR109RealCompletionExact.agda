{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact where

------------------------------------------------------------------------
-- B1 RECUT: USE THE ACTUAL FINITE PHYSICAL EXPECTATION SEQUENCE.
--
-- The older absolute R109 anchor carried an arbitrary `Nat -> Q` sequence.
-- The pinned finite physical family already owns the canonical absolute values
-- for every real cylinder observable:
--
--   F_k(O) = finiteExpectation family k O.
--
-- Hence no independent finite sequence should be chosen.  The remaining
-- physical theorem is only the quantitative comparison between the SAME R109
-- completed response and these concrete finite-family values, with the literal
-- rational Round109 tail embedded into R.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
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
    (embedding : Embed.OrderedRationalRealEmbedding)
  where

  finiteR109Expectation : Nat → ℝ
  finiteR109Expectation cutoff =
    Limit.finiteExpectation family cutoff observable

  embeddedR109Tail : Nat → ℝ
  embeddedR109Tail cutoff =
    Embed.embed embedding (Tail.r109RemainingTail source cutoff)

  record ConcreteFiniteR109RealCompletion
      (completedRationalExpectation : ℚ) : Set₁ where
    field
      completionUpperTail : ∀ cutoff →
        Embed.embed embedding completedRationalExpectation
        ≤ℝ finiteR109Expectation cutoff +ℝ embeddedR109Tail cutoff

  open ConcreteFiniteR109RealCompletion public

  finiteEndpointIsLiteralFamilyExpectation : ∀ cutoff →
    finiteR109Expectation cutoff
    ≡ Limit.finiteExpectation family cutoff observable
  finiteEndpointIsLiteralFamilyExpectation cutoff = refl

  arbitraryFiniteExpectationSequenceEliminated : Bool
  arbitraryFiniteExpectationSequenceEliminated = true

  remainingB1TheoremIsConcreteFamilyExpectationCompletionBound : Bool
  remainingB1TheoremIsConcreteFamilyExpectationCompletionBound = true
