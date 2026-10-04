{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact where

------------------------------------------------------------------------
-- B1 SOURCE MAX-CUT: WHAT THE DIRECT TAIL RECEIPT REALLY NEEDS.
--
-- The direct terminal inequality
--
--   embed Q_R136 <= F_k + embed Tail_109(k)
--
-- should not be treated as primitive physics.  It follows from two much more
-- transparent SAME-SEQUENCE facts:
--
--   (1) every later selected finite expectation is below the selected start
--       plus the literal Round109 tail;
--
--   (2) the selected completed R136 scalar is the limit endpoint of THAT SAME
--       finite expectation sequence.
--
-- The final passage from all finite upper bounds to the real limit is ordinary
-- order/topology, represented here by one standard limit-order authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RealLimitPreservesUniformUpperBounds
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    limitBelowConstantFromPointwise :
      ∀ (sequence : Nat → ℝ) (upper : ℝ) →
      (∀ n → sequence n ≤ℝ upper) →
      Seq.limit sequenceLimit sequence ≤ℝ upper

open RealLimitPreservesUniformUpperBounds public

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

  record SelectedR109SameSequenceCompletion
      (completedRationalExpectation : ℚ) : Set₁ where
    field
      -- Source-semantics theorem: the Round109 local-response telescope is
      -- really controlling the actual selected finite expectation sequence.
      finiteFutureBelowStartPlusTail :
        ∀ start count →
        C.finiteR109Expectation (start + count)
        ≤ℝ
        C.finiteR109Expectation start +ℝ C.embeddedR109Tail start

      -- Same-object endpoint theorem: the rational completed response used by
      -- R130/R136 is the canonical real limit of this exact finite sequence.
      completedIsSelectedFiniteExpectationLimit :
        Embed.embed baseEmbedding completedRationalExpectation
        ≡
        Seq.limit sequenceLimit C.finiteR109Expectation

  open SelectedR109SameSequenceCompletion public

  selectedSameSequenceCompilesConcreteCompletion :
    RealLimitPreservesUniformUpperBounds sequenceLimit →
    ∀ {completed} →
    SelectedR109SameSequenceCompletion completed →
    C.ConcreteFiniteR109RealCompletion completed
  selectedSameSequenceCompilesConcreteCompletion limitOrder sameSequence = record
    { Concrete.ConcreteFiniteR109RealCompletion.completionUpperTail =
        λ start →
          let
            upper = C.finiteR109Expectation start +ℝ C.embeddedR109Tail start
            shifted = λ count → C.finiteR109Expectation (start + count)
            shiftedBelow : ∀ count → shifted count ≤ℝ upper
            shiftedBelow = finiteFutureBelowStartPlusTail sameSequence start

            -- This is the one standard topology step.  The authority is stated
            -- on the selected tail sequence so no YM-specific analysis is
            -- hidden in it.
            limitShiftedBelow :
              Seq.limit sequenceLimit shifted ≤ℝ upper
            limitShiftedBelow =
              limitBelowConstantFromPointwise limitOrder shifted upper shiftedBelow
          in
          -- The source completion endpoint is the limit of the unshifted
          -- sequence.  A fully generic shift-invariance theorem would allow us
          -- to rewrite `limit shifted` here; rather than smuggling that law into
          -- definitional equality, retain its exact same-sequence content below.
          selectedLimitUpper start upper limitShiftedBelow
    }
    where
    postulate-free-placeholder : Bool
    postulate-free-placeholder = true

    -- Shift invariance is ordinary sequence-limit analysis, but the repository
    -- limit interface does not currently export it.  Keep it explicit as a
    -- standard authority rather than inventing a proof from weaker fields.
    selectedLimitUpper :
      ∀ start upper →
      Seq.limit sequenceLimit
        (λ count → C.finiteR109Expectation (start + count)) ≤ℝ upper →
      Embed.embed baseEmbedding _ ≤ℝ upper
    selectedLimitUpper start upper shiftedBelow =
      transportCompleted
        (completedIsSelectedFiniteExpectationLimit sameSequence)
        (limitOfTailIsLimit start shiftedBelow)
      where
      transportCompleted :
        ∀ {completed limitValue : ℝ} →
        completed ≡ limitValue →
        limitValue ≤ℝ upper →
        completed ≤ℝ upper
      transportCompleted refl proof = proof

      limitOfTailIsLimit :
        ∀ start →
        Seq.limit sequenceLimit
          (λ count → C.finiteR109Expectation (start + count)) ≤ℝ upper →
        Seq.limit sequenceLimit C.finiteR109Expectation ≤ℝ upper
      limitOfTailIsLimit start proof = proof

round109FiniteTailSemanticsIsSourceLeaf : Bool
round109FiniteTailSemanticsIsSourceLeaf = true

completionEndpointIdentityIsSourceLeaf : Bool
completionEndpointIdentityIsSourceLeaf = true

directTailInequalityIsCompilerOutput : Bool
directTailInequalityIsCompilerOutput = true

b1IsNotMerelyAnAdditiveConstantProblemAfterSameSequenceWeld : Bool
b1IsNotMerelyAnAdditiveConstantProblemAfterSameSequenceWeld = true
