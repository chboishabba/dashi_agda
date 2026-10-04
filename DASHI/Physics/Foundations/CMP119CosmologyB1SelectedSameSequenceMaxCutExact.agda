{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact where

------------------------------------------------------------------------
-- B1 SOURCE MAX-CUT: SELECTED SAME SEQUENCE, ALL CUTOFFS.
--
-- The terminal direct-tail inequality is compiler output once three exact
-- same-object facts are paid:
--
--   (1) Round109 controls every future value of the actual selected finite
--       expectation sequence by its literal tail;
--   (2) the R136 completed scalar is the limit of that SAME finite sequence;
--   (3) at every cutoff, that finite expectation is exactly the embedded
--       rational R144 finite D_Gamma readout.
--
-- (3) is deliberately all-cutoff.  This lets a later B2 geometric-tail theorem
-- choose whatever sufficiently late cutoff it needs without losing B1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RealTailLimitOrderAuthority
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    limitBelowConstantFromPointwise :
      ∀ (sequence : Nat → ℝ) (upper : ℝ) →
      (∀ n → sequence n ≤ℝ upper) →
      Seq.limit sequenceLimit sequence ≤ℝ upper

    finitePrefixDoesNotChangeLimit :
      ∀ (sequence : Nat → ℝ) start →
      Seq.limit sequenceLimit (λ count → sequence (start + count))
      ≡ Seq.limit sequenceLimit sequence

open RealTailLimitOrderAuthority public

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
      finiteFutureBelowStartPlusTail :
        ∀ start count →
        C.finiteR109Expectation (start + count)
        ≤ℝ
        C.finiteR109Expectation start +ℝ C.embeddedR109Tail start

      completedIsSelectedFiniteExpectationLimit :
        Embed.embed baseEmbedding completedRationalExpectation
        ≡
        Seq.limit sequenceLimit C.finiteR109Expectation

  open SelectedR109SameSequenceCompletion public

  record AllCutoffR144FiniteExpectationAttachment
      (finiteRationalDGamma : Nat → ℚ) : Set₁ where
    field
      finiteExpectationIsEmbeddedR144DGamma :
        ∀ cutoff →
        C.finiteR109Expectation cutoff
        ≡ Embed.embed baseEmbedding (finiteRationalDGamma cutoff)

  open AllCutoffR144FiniteExpectationAttachment public

  selectedSameSequenceCompilesConcreteCompletion :
    RealTailLimitOrderAuthority sequenceLimit →
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

            shiftedLimitBelow :
              Seq.limit sequenceLimit shifted ≤ℝ upper
            shiftedLimitBelow =
              limitBelowConstantFromPointwise
                limitOrder shifted upper shiftedBelow

            fullLimitBelow :
              Seq.limit sequenceLimit C.finiteR109Expectation ≤ℝ upper
            fullLimitBelow =
              subst
                (λ value → value ≤ℝ upper)
                (finitePrefixDoesNotChangeLimit
                  limitOrder C.finiteR109Expectation start)
                shiftedLimitBelow
          in
          subst
            (λ value → value ≤ℝ upper)
            (sym (completedIsSelectedFiniteExpectationLimit sameSequence))
            fullLimitBelow
    }

  directAnchorAtAnyCutoff :
    (limitOrder : RealTailLimitOrderAuthority sequenceLimit) →
    ∀ {completed finiteRationalDGamma} →
    SelectedR109SameSequenceCompletion completed →
    AllCutoffR144FiniteExpectationAttachment finiteRationalDGamma →
    ∀ cutoff →
    Direct.DirectR144R109TailAnchor
      embedding source completed (finiteRationalDGamma cutoff) cutoff
  directAnchorAtAnyCutoff
      limitOrder sameSequence finiteAttachment cutoff =
    Direct.fromConcreteCompletionAndFiniteIdentity
      family source observable embedding
      (selectedSameSequenceCompilesConcreteCompletion limitOrder sameSequence)
      (finiteExpectationIsEmbeddedR144DGamma finiteAttachment cutoff)

round109FiniteTailSemanticsIsSourceLeaf : Bool
round109FiniteTailSemanticsIsSourceLeaf = true

completionEndpointIdentityIsSourceLeaf : Bool
completionEndpointIdentityIsSourceLeaf = true

allCutoffR144FiniteAttachmentIsSourceLeaf : Bool
allCutoffR144FiniteAttachmentIsSourceLeaf = true

directTailInequalityIsCompilerOutput : Bool
directTailInequalityIsCompilerOutput = true

directB1AnchorCanFollowB2ToAnyLateCutoff : Bool
directB1AnchorCanFollowB2ToAnyLateCutoff = true

finitePrefixLimitLawIsGenericAnalysisNotYMPhysics : Bool
finitePrefixLimitLawIsGenericAnalysisNotYMPhysics = true
