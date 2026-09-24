module DASHI.Foundations.BishopSineCosineSetoidCongruenceExact where

------------------------------------------------------------------------
-- SETOID CONGRUENCE OF THE CONCRETE BISHOP SINE/COSINE LIMITS
--
-- The repository already owns:
--   * concrete signed factorial sine/cosine terms;
--   * termwise setoid congruence for those terms;
--   * exact identification of configured elementary terms with them;
--   * convergence of the configured elementary series;
--   * native Bishop finite-series extensionality and uniqueness of limits.
--
-- This module closes the remaining reducer:
--
--   x ≃ y  ->  sin_B(x) ≃ sin_B(y)
--   x ≃ y  ->  cos_B(x) ≃ cos_B(y)
--
-- for any configured elementary dataset whose terms are identified with the
-- concrete signed factorial terms.  No new analytic axiom is introduced.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity

open import DASHI.Physics.YangMills.CompactLieProofLevel

sineConfiguredTermCongruent :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  Concrete.ConcreteSineCosineTermIdentification dataSet →
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  ∀ index →
  BishopReal._≃_
    (Elementary.sineTerm dataSet left index)
    (Elementary.sineTerm dataSet right index)
sineConfiguredTermCongruent identification equivalent index =
  Parity.termCongruent
    (Concrete.identifiedSineOddTermFamily identification)
    equivalent
    index

cosineConfiguredTermCongruent :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  Concrete.ConcreteSineCosineTermIdentification dataSet →
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  ∀ index →
  BishopReal._≃_
    (Elementary.cosineTerm dataSet left index)
    (Elementary.cosineTerm dataSet right index)
cosineConfiguredTermCongruent identification equivalent index =
  Parity.termCongruent
    (Concrete.identifiedCosineEvenTermFamily identification)
    equivalent
    index

bishopSinCongruent :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  Concrete.ConcreteSineCosineTermIdentification dataSet →
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  BishopReal._≃_
    (Elementary.bishopSin dataSet left)
    (Elementary.bishopSin dataSet right)
bishopSinCongruent {dataSet = dataSet} identification equivalent =
  SeriesExt.termwiseEquivalentSeriesHaveEquivalentLimits
    (sineConfiguredTermCongruent identification equivalent)
    (Elementary.bishopSinConvergence dataSet _)
    (Elementary.bishopSinConvergence dataSet _)

bishopCosCongruent :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  Concrete.ConcreteSineCosineTermIdentification dataSet →
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  BishopReal._≃_
    (Elementary.bishopCos dataSet left)
    (Elementary.bishopCos dataSet right)
bishopCosCongruent {dataSet = dataSet} identification equivalent =
  SeriesExt.termwiseEquivalentSeriesHaveEquivalentLimits
    (cosineConfiguredTermCongruent identification equivalent)
    (Elementary.bishopCosConvergence dataSet _)
    (Elementary.bishopCosConvergence dataSet _)

record BishopTrigSetoidCongruenceReceipt
    (dataSet : Elementary.BishopElementaryPowerSeriesData) : Set₁ where
  constructor bishop-trig-setoid-congruence-receipt
  field
    identification :
      Concrete.ConcreteSineCosineTermIdentification dataSet

    sineCongruent :
      ∀ {left right : BishopReal.ℝ} →
      BishopReal._≃_ left right →
      BishopReal._≃_
        (Elementary.bishopSin dataSet left)
        (Elementary.bishopSin dataSet right)

    cosineCongruent :
      ∀ {left right : BishopReal.ℝ} →
      BishopReal._≃_ left right →
      BishopReal._≃_
        (Elementary.bishopCos dataSet left)
        (Elementary.bishopCos dataSet right)

open BishopTrigSetoidCongruenceReceipt public

canonicalBishopTrigSetoidCongruenceReceipt :
  ∀ {dataSet} →
  Concrete.ConcreteSineCosineTermIdentification dataSet →
  BishopTrigSetoidCongruenceReceipt dataSet
canonicalBishopTrigSetoidCongruenceReceipt identification =
  bishop-trig-setoid-congruence-receipt
    identification
    (bishopSinCongruent identification)
    (bishopCosCongruent identification)

bishopSineCosineSetoidCongruenceReducerLevel : ProofLevel
bishopSineCosineSetoidCongruenceReducerLevel = machineChecked

bishopSineCosineConcreteTermIdentificationLevel : ProofLevel
bishopSineCosineConcreteTermIdentificationLevel = conditional
