module DASHI.Physics.Foundations.CMP119WilsonGibbsVanishingInsertionTraceNoGoExact where

------------------------------------------------------------------------
-- FIRST NONCLASSICAL SOURCE TEST ON THE LITERAL FINITE MEASURE
--
-- For the selected d=4 Wilson metric action, the classical action trace
-- cancels pointwise. If the selected insertion has a vanishing diagonal
-- Weyl/trace derivative as well, the *actual finite Haar connected*
-- numerator has zero diagonal sum. Therefore strict negative active sum
-- cannot follow from that insertion. A nonzero insertion trace, an
-- independently proved anomaly/counterterm, or a different physical
-- stress source must be established to escape this obstruction.
--
-- This is NOT a proof of a renormalized continuum trace anomaly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (trans; subst)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as Trace
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (selected : Wilson.ClassicalWilsonSelectedInsertion Configuration)
    (laws : Integral.RationalFiniteMeasureIntegrationLaws measure)
  where

  selectedWeylInsertionTrace :
    Configuration → ℚ
  selectedWeylInsertionTrace configuration =
    Wilson.insertionVariation selected K.component00 configuration
    + Wilson.insertionVariation selected K.component11 configuration
    + Wilson.insertionVariation selected K.component22 configuration
    + Wilson.insertionVariation selected K.component33 configuration

  traceInsertionIsSelectedWeylTrace :
    (configuration : Configuration) →
    Trace.traceInsertionVariation selected laws configuration
    ≡ selectedWeylInsertionTrace configuration
  traceInsertionIsSelectedWeylTrace configuration =
    Agda.Builtin.Equality.refl

  record TraceSilentInsertion : Set where
    field
      selectedWeylTraceZero :
        (configuration : Configuration) →
        selectedWeylInsertionTrace configuration ≡ 0ℚ

  open TraceSilentInsertion public

  selectedWeightedTraceZero :
    (silent : TraceSilentInsertion)
    (configuration : Configuration) →
    Physical.density measure configuration
      * Trace.traceInsertionVariation selected laws configuration
    ≡ 0ℚ
  selectedWeightedTraceZero silent configuration
      rewrite traceInsertionIsSelectedWeylTrace configuration
            | selectedWeylTraceZero silent configuration =
    Ring.solve-∀ (Physical.density measure configuration)

  selectedHaarTraceNumeratorZero :
    (silent : TraceSilentInsertion) →
    Trace.traceInsertionNumerator selected laws ≡ 0ℚ
  selectedHaarTraceNumeratorZero silent =
    trans
      (Integral.haarIntegralCongruent laws
        (λ configuration →
          Physical.density measure configuration
            * Trace.traceInsertionVariation selected laws configuration)
        (λ _ → 0ℚ)
        (selectedWeightedTraceZero silent))
      (Integral.haarIntegralZero laws)

  selectedConnectedActiveSumZero :
    (silent : TraceSilentInsertion) →
    Trace.activeConnectedNumerator selected laws ≡ 0ℚ
  selectedConnectedActiveSumZero silent
      rewrite Trace.activeConnectedNumeratorIsPartitionTimesTraceInsertion
                selected laws
            | selectedHaarTraceNumeratorZero silent =
    Ring.solve-∀ (Physical.partitionFunction measure)

  selectedNegativeActiveRulesOutTraceSilence :
    Trace.activeConnectedNumerator selected laws < 0ℚ →
    TraceSilentInsertion → ⊥
  selectedNegativeActiveRulesOutTraceSilence negative silent =
    ℚP.<-irrefl 0ℚ
      (subst
        (λ value → value < 0ℚ)
        (selectedConnectedActiveSumZero silent)
        negative)
