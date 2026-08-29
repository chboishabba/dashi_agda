{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact where

------------------------------------------------------------------------
-- ROUND116: DIVISION-FREE NORMALIZED SOURCE DERIVATIVE -> STRESS INSERTION
--
-- CMP119 expands numerator and denominator of one normalized local expectation
-- together.  The repository already owns the division-free cross numerator
--
--                     N' Z - N Z'.
--
-- Rather than introducing an inverse/quotient theorem, represent the physical
-- first source derivative by this connected cross numerator.  Once the literal
-- metric/source variation identifies the surviving connected numerator with the
-- stress insertion, the same CMP119 insertion can feed the Round109 telescope.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross

record NormalizedSourceDerivativeCrossData : Set₁ where
  field
    numerator denominator : ℚ
    numeratorDerivative denominatorDerivative : ℚ
    connectedInsertionNumerator : ℚ

    -- Physical/source identification after common vacuum pieces cancel in the
    -- normalized numerator/denominator pair.
    crossNumeratorIsConnectedInsertion :
      Cross.normalizedCrossNumerator
        numerator denominator numeratorDerivative denominatorDerivative
      ≡ connectedInsertionNumerator
open NormalizedSourceDerivativeCrossData public

sourceDerivativeCrossNumerator : NormalizedSourceDerivativeCrossData → ℚ
sourceDerivativeCrossNumerator dataSet =
  numeratorDerivative dataSet * denominator dataSet
    - numerator dataSet * denominatorDerivative dataSet

sourceDerivativeCrossNumeratorIsConnectedInsertion :
  (dataSet : NormalizedSourceDerivativeCrossData) →
  sourceDerivativeCrossNumerator dataSet
  ≡ connectedInsertionNumerator dataSet
sourceDerivativeCrossNumeratorIsConnectedInsertion dataSet =
  crossNumeratorIsConnectedInsertion dataSet

record MetricStressNormalizedInsertionWeld : Set₁ where
  field
    normalizedSource : NormalizedSourceDerivativeCrossData
    metricFirstVariationCrossNumerator : ℚ
    cmp119StressInsertionNumerator : ℚ

    metricVariationIsNormalizedCrossNumerator :
      metricFirstVariationCrossNumerator
      ≡ sourceDerivativeCrossNumerator normalizedSource

    connectedInsertionIsCMP119StressInsertion :
      connectedInsertionNumerator normalizedSource
      ≡ cmp119StressInsertionNumerator
open MetricStressNormalizedInsertionWeld public

metricVariationCrossNumeratorIsCMP119StressInsertion :
  (dataSet : MetricStressNormalizedInsertionWeld) →
  metricFirstVariationCrossNumerator dataSet
  ≡ cmp119StressInsertionNumerator dataSet
metricVariationCrossNumeratorIsCMP119StressInsertion dataSet =
  trans
    (metricVariationIsNormalizedCrossNumerator dataSet)
    (trans
      (sourceDerivativeCrossNumeratorIsConnectedInsertion
        (normalizedSource dataSet))
      (connectedInsertionIsCMP119StressInsertion dataSet))

normalizedStressInsertionCompilerLevel : ProofLevel
normalizedStressInsertionCompilerLevel = machineChecked

-- Remaining physical source binding: on the literal finite Balaban density,
-- identify the metric/source derivative numerator and denominator with the
-- CMP119 normalized local-insertion pair and prove that the surviving connected
-- cross numerator is the selected stress insertion.  The cancellation algebra
-- and downstream telescope are already owned.
literalMetricVariationToCMP119StressInsertionLevel : ProofLevel
literalMetricVariationToCMP119StressInsertionLevel = conditional
