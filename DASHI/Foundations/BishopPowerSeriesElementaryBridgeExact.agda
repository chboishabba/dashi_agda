module DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (ℚᵘ)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Power-series functions on Bishop's constructive reals.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354.  No DOI assigned.
--
-- Murray's library proves Cauchy completeness, uniqueness of limits, the Cauchy
-- test for series and absolute convergence implying convergence.  It does not
-- itself define sine, cosine, exponential or logarithm on main.  DASHI owns the
-- coefficient/tail proofs, while Bishop supplies the concrete completion.
------------------------------------------------------------------------

record AbsolutelyConvergentBishopSeries : Set₁ where
  field
    term : Nat → Bishop.Bishopℝ
    absoluteConvergence :
      Bishop.BishopAbsoluteSeriesConvergent term

open AbsolutelyConvergentBishopSeries public

seriesValue : AbsolutelyConvergentBishopSeries → Bishop.Bishopℝ
seriesValue series =
  Bishop.bishopSeriesLimit
    (term series)
    (absoluteConvergence series)

seriesValueConvergence :
  (series : AbsolutelyConvergentBishopSeries) →
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf (term series))
    (seriesValue series)
seriesValueConvergence series =
  Bishop.bishopSeriesLimitConvergence
    (term series)
    (absoluteConvergence series)

seriesValueUnique :
  (series : AbsolutelyConvergentBishopSeries) →
  ∀ {other : Bishop.Bishopℝ} →
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf (term series)) other →
  Bishop.BishopEquivalent (seriesValue series) other
seriesValueUnique series =
  Bishop.bishopSeriesLimitUnique
    (term series)
    (absoluteConvergence series)

record BishopElementaryPowerSeriesData : Set₁ where
  field
    rational : ℚᵘ → Bishop.Bishopℝ
    rationalDefinition : rational ≡ BishopReal._⋆

    sineTerm cosineTerm exponentialTerm :
      Bishop.Bishopℝ → Nat → Bishop.Bishopℝ

    negativeLogOneMinusTerm :
      Bishop.Bishopℝ → Nat → Bishop.Bishopℝ

    sineAbsoluteConvergence : ∀ point →
      Bishop.BishopAbsoluteSeriesConvergent (sineTerm point)

    cosineAbsoluteConvergence : ∀ point →
      Bishop.BishopAbsoluteSeriesConvergent (cosineTerm point)

    exponentialAbsoluteConvergence : ∀ point →
      Bishop.BishopAbsoluteSeriesConvergent (exponentialTerm point)

    InOpenUnitInterval : Bishop.Bishopℝ → Set

    negativeLogAbsoluteConvergence : ∀ point →
      InOpenUnitInterval point →
      Bishop.BishopAbsoluteSeriesConvergent
        (negativeLogOneMinusTerm point)

    -- Coefficient recurrences pin the intended power series.  They prevent a
    -- caller from satisfying the convergence fields with unrelated sequences.
    sineCoefficientRecurrenceExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    cosineCoefficientRecurrenceExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    exponentialCoefficientRecurrenceExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    negativeLogCoefficientRecurrenceExact : (point : Bishop.Bishopℝ) (index : Nat) → Set

    sineOddPowersAndFactorialsExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    cosineEvenPowersAndFactorialsExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    exponentialPowersAndFactorialsExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    negativeLogPowersOverPositiveIntegersExact : (point : Bishop.Bishopℝ) (index : Nat) → Set

    sineAlternatingSignsExact : (point : Bishop.Bishopℝ) (index : Nat) → Set
    cosineAlternatingSignsExact : (point : Bishop.Bishopℝ) (index : Nat) → Set

open BishopElementaryPowerSeriesData public

sineSeries :
  BishopElementaryPowerSeriesData →
  Bishop.Bishopℝ →
  AbsolutelyConvergentBishopSeries
sineSeries dataSet point = record
  { term = sineTerm dataSet point
  ; absoluteConvergence = sineAbsoluteConvergence dataSet point
  }

cosineSeries :
  BishopElementaryPowerSeriesData →
  Bishop.Bishopℝ →
  AbsolutelyConvergentBishopSeries
cosineSeries dataSet point = record
  { term = cosineTerm dataSet point
  ; absoluteConvergence = cosineAbsoluteConvergence dataSet point
  }

exponentialSeries :
  BishopElementaryPowerSeriesData →
  Bishop.Bishopℝ →
  AbsolutelyConvergentBishopSeries
exponentialSeries dataSet point = record
  { term = exponentialTerm dataSet point
  ; absoluteConvergence = exponentialAbsoluteConvergence dataSet point
  }

negativeLogOneMinusSeries :
  (dataSet : BishopElementaryPowerSeriesData) →
  (point : Bishop.Bishopℝ) →
  InOpenUnitInterval dataSet point →
  AbsolutelyConvergentBishopSeries
negativeLogOneMinusSeries dataSet point inUnit = record
  { term = negativeLogOneMinusTerm dataSet point
  ; absoluteConvergence =
      negativeLogAbsoluteConvergence dataSet point inUnit
  }

bishopSin bishopCos bishopExp :
  BishopElementaryPowerSeriesData →
  Bishop.Bishopℝ →
  Bishop.Bishopℝ
bishopSin dataSet point = seriesValue (sineSeries dataSet point)
bishopCos dataSet point = seriesValue (cosineSeries dataSet point)
bishopExp dataSet point = seriesValue (exponentialSeries dataSet point)

bishopNegativeLogOneMinus :
  (dataSet : BishopElementaryPowerSeriesData) →
  (point : Bishop.Bishopℝ) →
  InOpenUnitInterval dataSet point →
  Bishop.Bishopℝ
bishopNegativeLogOneMinus dataSet point inUnit =
  seriesValue (negativeLogOneMinusSeries dataSet point inUnit)

bishopSinConvergence :
  (dataSet : BishopElementaryPowerSeriesData) →
  (point : Bishop.Bishopℝ) →
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf (sineTerm dataSet point))
    (bishopSin dataSet point)
bishopSinConvergence dataSet point =
  seriesValueConvergence (sineSeries dataSet point)

bishopCosConvergence :
  (dataSet : BishopElementaryPowerSeriesData) →
  (point : Bishop.Bishopℝ) →
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf (cosineTerm dataSet point))
    (bishopCos dataSet point)
bishopCosConvergence dataSet point =
  seriesValueConvergence (cosineSeries dataSet point)

bishopExpConvergence :
  (dataSet : BishopElementaryPowerSeriesData) →
  (point : Bishop.Bishopℝ) →
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf (exponentialTerm dataSet point))
    (bishopExp dataSet point)
bishopExpConvergence dataSet point =
  seriesValueConvergence (exponentialSeries dataSet point)

bishopNegativeLogConvergence :
  (dataSet : BishopElementaryPowerSeriesData) →
  (point : Bishop.Bishopℝ) →
  (inUnit : InOpenUnitInterval dataSet point) →
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf
      (negativeLogOneMinusTerm dataSet point))
    (bishopNegativeLogOneMinus dataSet point inUnit)
bishopNegativeLogConvergence dataSet point inUnit =
  seriesValueConvergence
    (negativeLogOneMinusSeries dataSet point inUnit)

------------------------------------------------------------------------
-- The remaining elementary-function proof is finite coefficient/tail work.
-- Completeness and choice of the limit are no longer authority fields.
------------------------------------------------------------------------

record BishopConfiguredElementaryTailProofs
    (dataSet : BishopElementaryPowerSeriesData) : Set₁ where
  field
    configuredRadius : Bishop.Bishopℝ
    InConfiguredRadius : Bishop.Bishopℝ → Set

    sineTermMagnitudeDecreasing : (point : Bishop.Bishopℝ) (index : Nat) →
      InConfiguredRadius point → Set
    cosineTermMagnitudeDecreasing : (point : Bishop.Bishopℝ) (index : Nat) →
      InConfiguredRadius point → Set

    sineCubicSignedRemainder : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set
    sineQuinticSignedRemainder : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set
    cosineQuadraticSignedRemainder : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set
    cosineQuarticSignedRemainder : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set

    sineCubicFirstOmittedBound : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set
    sineQuinticFirstOmittedBound : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set
    cosineQuadraticFirstOmittedBound : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set
    cosineQuarticFirstOmittedBound : (point : Bishop.Bishopℝ) →
      InConfiguredRadius point → Set

    negativeLogOneMinusBound : (point : Bishop.Bishopℝ) (inUnit : InOpenUnitInterval dataSet point) → Set
    positiveExponentialTail : (point : Bishop.Bishopℝ) → Set
    logarithmMonotoneOnPositive : Set
    logarithmExponentialInverse : Set

open BishopConfiguredElementaryTailProofs public

bishopPowerSeriesDefinitionsLevel : ProofLevel
bishopPowerSeriesDefinitionsLevel = machineChecked

bishopPowerSeriesCompletenessLevel : ProofLevel
bishopPowerSeriesCompletenessLevel = machineChecked

bishopElementaryCoefficientTailInputsLevel : ProofLevel
bishopElementaryCoefficientTailInputsLevel = conditional
