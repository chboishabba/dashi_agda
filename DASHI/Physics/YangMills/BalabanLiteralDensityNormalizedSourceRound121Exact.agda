{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact where

------------------------------------------------------------------------
-- ROUND121: NORMALIZED STRESS SOURCE LIVES ON THE LITERAL BETA-DRIVEN DENSITY
--
-- `Balaban1989BetaDrivenCompleteDensityFlowExact` already eliminates the
-- parallel-trajectory loophole: `densityAt k` is on the same beta history used
-- by the finite source flow.  This file eliminates the analogous parallel-
-- density loophole for the normalized stress insertion.  Numerator,
-- denominator and their metric derivatives are functions of that literal
-- Density, and Round116 cross data is constructed only at `densityAt scale`.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116

record LiteralDensityNormalizedStressSource
    {trajectory split}
    (inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₁ where
  field
    MetricPerturbation : Set

    numerator denominator : BetaDensity.Density inputs → ℚ
    numeratorDerivative denominatorDerivative :
      BetaDensity.Density inputs → MetricPerturbation → ℚ
    connectedInsertionNumerator :
      BetaDensity.Density inputs → MetricPerturbation → ℚ

    -- The source calculus is stated on every literal density value, so selecting
    -- an RG scale below cannot silently change the carrier.
    normalizedCrossNumeratorIsConnectedInsertion :
      ∀ density perturbation →
      Cross.normalizedCrossNumerator
        (numerator density)
        (denominator density)
        (numeratorDerivative density perturbation)
        (denominatorDerivative density perturbation)
      ≡ connectedInsertionNumerator density perturbation
open LiteralDensityNormalizedStressSource public

crossDataAt :
  ∀ {trajectory split inputs}
    (dataSet : LiteralDensityNormalizedStressSource
      {trajectory = trajectory} {split = split} inputs) →
  Nat → MetricPerturbation dataSet →
  R116.NormalizedSourceDerivativeCrossData
crossDataAt {inputs = inputs} dataSet scale perturbation =
  let density = BetaDensity.densityAt inputs scale
  in record
    { R116.NormalizedSourceDerivativeCrossData.numerator =
        numerator dataSet density
    ; R116.NormalizedSourceDerivativeCrossData.denominator =
        denominator dataSet density
    ; R116.NormalizedSourceDerivativeCrossData.numeratorDerivative =
        numeratorDerivative dataSet density perturbation
    ; R116.NormalizedSourceDerivativeCrossData.denominatorDerivative =
        denominatorDerivative dataSet density perturbation
    ; R116.NormalizedSourceDerivativeCrossData.connectedInsertionNumerator =
        connectedInsertionNumerator dataSet density perturbation
    ; R116.NormalizedSourceDerivativeCrossData.crossNumeratorIsConnectedInsertion =
        normalizedCrossNumeratorIsConnectedInsertion dataSet density perturbation
    }

literalDensityCrossNumeratorIsConnectedInsertion :
  ∀ {trajectory split inputs}
    (dataSet : LiteralDensityNormalizedStressSource
      {trajectory = trajectory} {split = split} inputs)
    scale perturbation →
  R116.sourceDerivativeCrossNumerator (crossDataAt dataSet scale perturbation)
  ≡ connectedInsertionNumerator dataSet
      (BetaDensity.densityAt inputs scale) perturbation
literalDensityCrossNumeratorIsConnectedInsertion dataSet scale perturbation =
  R116.sourceDerivativeCrossNumeratorIsConnectedInsertion
    (crossDataAt dataSet scale perturbation)

literalDensityNormalizedSourceCompilerLevel : ProofLevel
literalDensityNormalizedSourceCompilerLevel = machineChecked

-- Physical finite-density analysis still required: define numerator/denominator
-- as the actual normalized expectation integrals of the CMP119 insertion class
-- and prove the displayed metric derivative/cross-numerator identity on the
-- literal Section-2 density.  No separate density or trajectory may be used.
literalBalabanDensityNumeratorDenominatorMetricDerivativeLevel : ProofLevel
literalBalabanDensityNumeratorDenominatorMetricDerivativeLevel = conditional
