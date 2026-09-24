{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact where

open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- LITERAL FINITE-MEASURE CALCULUS -> CONCRETE R121 DENSITY SOURCE
--
-- R121 previously exposed the correct same-beta-density ABI, but the repository
-- had no constructor inhabiting LiteralDensityNormalizedStressSource.
--
-- R124 already maps every beta-driven density to the literal finite Clay
-- measure.  Therefore the least-privilege missing object is a normalized stress
-- calculus *on that finite measure*.  Composing it with densityToFiniteMeasure
-- constructs R121 definitionally and removes the abstract density callback.
------------------------------------------------------------------------

record LiteralFiniteMeasureNormalizedStressCalculus
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (measureWeld :
      R124.BalabanDensityLiteralFiniteMeasureWeld
        {trajectory = trajectory} {split = split} {inputs = inputs}
        Y group) : Set₁ where
  field
    MetricPerturbation : Set

    numerator denominator :
      Top.FiniteMeasure C → ℚ

    numeratorDerivative denominatorDerivative :
      Top.FiniteMeasure C → MetricPerturbation → ℚ

    connectedInsertionNumerator :
      Top.FiniteMeasure C → MetricPerturbation → ℚ

    normalizedCrossNumeratorIsConnectedInsertion :
      ∀ measure perturbation →
      Cross.normalizedCrossNumerator
        (numerator measure)
        (denominator measure)
        (numeratorDerivative measure perturbation)
        (denominatorDerivative measure perturbation)
      ≡ connectedInsertionNumerator measure perturbation

open LiteralFiniteMeasureNormalizedStressCalculus public

asLiteralDensityNormalizedStressSource :
  ∀ {trajectory split inputs C S Y group}
    {measureWeld :
      R124.BalabanDensityLiteralFiniteMeasureWeld
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} Y group} →
  LiteralFiniteMeasureNormalizedStressCalculus measureWeld →
  R121.LiteralDensityNormalizedStressSource inputs
asLiteralDensityNormalizedStressSource {measureWeld = measureWeld} calculus =
  record
    { R121.LiteralDensityNormalizedStressSource.MetricPerturbation =
        MetricPerturbation calculus
    ; R121.LiteralDensityNormalizedStressSource.numerator =
        λ density →
          numerator calculus
            (R124.densityToFiniteMeasure measureWeld density)
    ; R121.LiteralDensityNormalizedStressSource.denominator =
        λ density →
          denominator calculus
            (R124.densityToFiniteMeasure measureWeld density)
    ; R121.LiteralDensityNormalizedStressSource.numeratorDerivative =
        λ density perturbation →
          numeratorDerivative calculus
            (R124.densityToFiniteMeasure measureWeld density)
            perturbation
    ; R121.LiteralDensityNormalizedStressSource.denominatorDerivative =
        λ density perturbation →
          denominatorDerivative calculus
            (R124.densityToFiniteMeasure measureWeld density)
            perturbation
    ; R121.LiteralDensityNormalizedStressSource.connectedInsertionNumerator =
        λ density perturbation →
          connectedInsertionNumerator calculus
            (R124.densityToFiniteMeasure measureWeld density)
            perturbation
    ; R121.LiteralDensityNormalizedStressSource.normalizedCrossNumeratorIsConnectedInsertion =
        λ density perturbation →
          normalizedCrossNumeratorIsConnectedInsertion calculus
            (R124.densityToFiniteMeasure measureWeld density)
            perturbation
    }

connectedNumeratorAtBetaScaleIsFiniteMeasureNumerator :
  ∀ {trajectory split inputs C S Y group}
    {measureWeld :
      R124.BalabanDensityLiteralFiniteMeasureWeld
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} Y group}
    (calculus : LiteralFiniteMeasureNormalizedStressCalculus measureWeld)
    scale perturbation →
  R121.connectedInsertionNumerator
    (asLiteralDensityNormalizedStressSource calculus)
    (Beta.densityAt inputs scale)
    perturbation
  ≡
  connectedInsertionNumerator calculus
    (Top.finiteMeasure Y group (R124.cutoffAtScale measureWeld scale))
    perturbation
connectedNumeratorAtBetaScaleIsFiniteMeasureNumerator
    {measureWeld = measureWeld} calculus scale perturbation
    rewrite R124.densityAtScaleIsLiteralFiniteMeasure measureWeld scale =
  Relation.Binary.PropositionalEquality.refl
