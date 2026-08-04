module DASHI.Physics.YangMills.BalabanBishopConcreteSeriesConvergenceTransportExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- The round-nine parity surface carried transformed-series convergence as a
-- separate analytic field.  Bishop's Sequence.agda already proves convergence
-- transport under pointwise setoid equivalence and under negation.  This module
-- specializes those results to partial sums, proving that term parity alone is
-- sufficient to construct the transformed convergence witnesses consumed by
-- bishopSinNeg and bishopCosNeg.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as ParityLimit
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite partial sums respect termwise Bishop equivalence.
------------------------------------------------------------------------

seriesOfPointwiseEquivalent :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal._≃_ (left index) (right index)) →
  ∀ count →
  BishopReal._≃_
    (BishopSequence.SeriesOf left count)
    (BishopSequence.SeriesOf right count)
seriesOfPointwiseEquivalent termwise =
  BishopSequence.∑₀-cong termwise

pointwiseEquivalentSeriesConvergence :
  ∀ {left right : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  (∀ index → BishopReal._≃_ (left index) (right index)) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf left) limit →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf right) limit
pointwiseEquivalentSeriesConvergence
    {left = left} {right = right} {limit = limit}
    termwise convergence =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ index → seriesOfPointwiseEquivalent termwise index)
    (limit , convergence)

pointwiseEquivalentSeriesConvergenceFromRight :
  ∀ {left right : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  (∀ index → BishopReal._≃_ (left index) (right index)) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf right) limit →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf left) limit
pointwiseEquivalentSeriesConvergenceFromRight termwise convergence =
  pointwiseEquivalentSeriesConvergence
    (λ index → BishopProperties.≃-symm (termwise index))
    convergence

------------------------------------------------------------------------
-- Negation commutes with every finite partial sum and hence with its limit.
------------------------------------------------------------------------

seriesOfNegatedTermsEquivalentNegatedSeries :
  (term : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopSequence.SeriesOf (λ index → BishopReal.- (term index)) count)
    (BishopReal.- (BishopSequence.SeriesOf term count))
seriesOfNegatedTermsEquivalentNegatedSeries term zero =
  BishopProperties.0≃-0
seriesOfNegatedTermsEquivalentNegatedSeries term (suc count) =
  BishopProperties.≃-trans
    (BishopProperties.+-cong
      (seriesOfNegatedTermsEquivalentNegatedSeries term count)
      BishopProperties.≃-refl)
    (BishopProperties.≃-symm
      (BishopProperties.neg-distrib-+
        (BishopSequence.SeriesOf term count)
        (term count)))

seriesNegationConvergence :
  ∀ {term : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf term) limit →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (λ index → BishopReal.- (term index)))
    (BishopReal.- limit)
seriesNegationConvergence {term = term} {limit = limit} convergence =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ index →
      BishopProperties.≃-symm
        (seriesOfNegatedTermsEquivalentNegatedSeries term index))
    (BishopReal.- limit ,
      BishopSequence.-xₙ→-x₀ (limit , convergence))

------------------------------------------------------------------------
-- Term parity now constructs the formerly independent convergence fields.
------------------------------------------------------------------------

sineSeriesAtNegConvergesFromTermOddness :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  ParityLimit.BishopOddTermFamily
    (Elementary.sineTerm dataSet) →
  ∀ point →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Elementary.sineTerm dataSet (BishopReal.- point)))
    (BishopReal.- (Elementary.bishopSin dataSet point))
sineSeriesAtNegConvergesFromTermOddness
    {dataSet = dataSet} oddTerms point =
  pointwiseEquivalentSeriesConvergenceFromRight
    (ParityLimit.BishopOddTermFamily.termOdd oddTerms point)
    (seriesNegationConvergence
      (Elementary.bishopSinConvergence dataSet point))

cosineSeriesAtNegConvergesFromTermEvenness :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  ParityLimit.BishopEvenTermFamily
    (Elementary.cosineTerm dataSet) →
  ∀ point →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Elementary.cosineTerm dataSet (BishopReal.- point)))
    (Elementary.bishopCos dataSet point)
cosineSeriesAtNegConvergesFromTermEvenness
    {dataSet = dataSet} evenTerms point =
  pointwiseEquivalentSeriesConvergenceFromRight
    (ParityLimit.BishopEvenTermFamily.termEven evenTerms point)
    (Elementary.bishopCosConvergence dataSet point)

bishopSeriesLimitParityInputsFromTermParity :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  ParityLimit.BishopOddTermFamily
    (Elementary.sineTerm dataSet) →
  ParityLimit.BishopEvenTermFamily
    (Elementary.cosineTerm dataSet) →
  ParityLimit.BishopSeriesLimitParityInputs dataSet
bishopSeriesLimitParityInputsFromTermParity sineOdd cosineEven = record
  { sineTermsOdd = sineOdd
  ; cosineTermsEven = cosineEven
  ; sineSeriesAtNegConvergesToNegatedValue =
      sineSeriesAtNegConvergesFromTermOddness sineOdd
  ; cosineSeriesAtNegConvergesToSameValue =
      cosineSeriesAtNegConvergesFromTermEvenness cosineEven
  }

bishopPointwiseSeriesTransportLevel : ProofLevel
bishopPointwiseSeriesTransportLevel = machineChecked

bishopSeriesNegationTransportLevel : ProofLevel
bishopSeriesNegationTransportLevel = machineChecked

bishopTransformedSeriesConvergenceFromParityLevel : ProofLevel
bishopTransformedSeriesConvergenceFromParityLevel = machineChecked
