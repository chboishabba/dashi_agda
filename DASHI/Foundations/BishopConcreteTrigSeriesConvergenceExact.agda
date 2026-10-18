module DASHI.Foundations.BishopConcreteTrigSeriesConvergenceExact where

------------------------------------------------------------------------
-- CONCRETE SIGNED-FACTORIAL SINE/COSINE SERIES CONVERGENCE
--
-- This extracts the convergence part already present in the Round11
-- factor-interchange lane, without importing derivative-interchange control.
--
-- Source:
--   * Round11 elementary Bishop sine/cosine series;
--   * machine-produced configured term identification;
--   * pointwise-equivalent series convergence transport.
--
-- Result:
--   the literal concrete signed-factorial term families converge to the
--   configured Bishop sine/cosine values.
------------------------------------------------------------------------

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopConcreteSeriesConvergenceTransportExact as Transport
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

open import DASHI.Physics.YangMills.CompactLieProofLevel

dataSet :
  Round11.Round11BishopCutset →
  Elementary.BishopElementaryPowerSeriesData
dataSet inputs = Round11.elementarySeries inputs

termIdentification :
  (inputs : Round11.Round11BishopCutset) →
  Terms.ConcreteSineCosineTermIdentification (dataSet inputs)
termIdentification inputs =
  Round11.round11ConcreteTermIdentification inputs

concreteSineSeriesConverges :
  (inputs : Round11.Round11BishopCutset) →
  (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
    (Elementary.bishopSin (dataSet inputs) point)
concreteSineSeriesConverges inputs point =
  Transport.pointwiseEquivalentSeriesConvergence
    (Terms.sineTermIsConcrete
      (termIdentification inputs)
      point)
    (Elementary.bishopSinConvergence
      (dataSet inputs)
      point)

concreteCosineSeriesConverges :
  (inputs : Round11.Round11BishopCutset) →
  (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.cosineSignedTerm point))
    (Elementary.bishopCos (dataSet inputs) point)
concreteCosineSeriesConverges inputs point =
  Transport.pointwiseEquivalentSeriesConvergence
    (Terms.cosineTermIsConcrete
      (termIdentification inputs)
      point)
    (Elementary.bishopCosConvergence
      (dataSet inputs)
      point)

record BishopConcreteTrigConvergenceReceipt
    (inputs : Round11.Round11BishopCutset) : Set₁ where
  constructor bishop-concrete-trig-convergence-receipt
  field
    sine :
      ∀ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
        (Elementary.bishopSin (dataSet inputs) point)

    cosine :
      ∀ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Terms.cosineSignedTerm point))
        (Elementary.bishopCos (dataSet inputs) point)

open BishopConcreteTrigConvergenceReceipt public

canonicalBishopConcreteTrigConvergenceReceipt :
  (inputs : Round11.Round11BishopCutset) →
  BishopConcreteTrigConvergenceReceipt inputs
canonicalBishopConcreteTrigConvergenceReceipt inputs =
  bishop-concrete-trig-convergence-receipt
    (concreteSineSeriesConverges inputs)
    (concreteCosineSeriesConverges inputs)

bishopConcreteTrigSeriesConvergenceLevel : ProofLevel
bishopConcreteTrigSeriesConvergenceLevel = machineChecked
