{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact where

------------------------------------------------------------------------
-- ROUND116: DIVISION-FREE NORMALIZED SOURCE DERIVATIVE -> LITERAL CMP119 INSERTION
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source

record NormalizedSourceDerivativeCrossData : Set₁ where
  field
    numerator denominator : ℚ
    numeratorDerivative denominatorDerivative : ℚ
    connectedInsertionNumerator : ℚ

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

    -- Literal CMP119 identity, not merely a rational value with a suggestive
    -- name.  The evaluator exposes the normalized insertion numerator for the
    -- exact source-native insertion pair consumed by the telescope lane.
    source : Source.CMP119CompatibleLocalExpectationFlow
    stressInsertion : Source.SourceNativeOrdinaryCharacteristicPair source
    localInsertionNumerator : Source.LocalInsertionPair source → ℚ

    metricVariationIsNormalizedCrossNumerator :
      metricFirstVariationCrossNumerator
      ≡ sourceDerivativeCrossNumerator normalizedSource

    connectedInsertionIsSelectedCMP119StressInsertion :
      connectedInsertionNumerator normalizedSource
      ≡ localInsertionNumerator (Source.pair stressInsertion)
open MetricStressNormalizedInsertionWeld public

cmp119StressInsertionNumerator : MetricStressNormalizedInsertionWeld → ℚ
cmp119StressInsertionNumerator dataSet =
  localInsertionNumerator dataSet (Source.pair (stressInsertion dataSet))

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
      (connectedInsertionIsSelectedCMP119StressInsertion dataSet))

normalizedStressInsertionCompilerLevel : ProofLevel
normalizedStressInsertionCompilerLevel = machineChecked

-- Remaining physical source binding: instantiate numerator/denominator and their
-- metric derivatives on the literal finite Balaban density, and identify the
-- surviving connected cross numerator with the exact CMP119 insertion object.
literalMetricVariationToCMP119StressInsertionLevel : ProofLevel
literalMetricVariationToCMP119StressInsertionLevel = conditional
