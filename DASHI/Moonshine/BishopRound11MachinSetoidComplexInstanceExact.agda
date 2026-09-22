module DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact where

------------------------------------------------------------------------
-- ACTUAL ROUTE-B SOURCE TRANSCENDENTALS
--
-- For any selected Round11 Bishop cutset, instantiate the setoid-native
-- complex package with:
--
--   * Round11's configured sine/cosine power-series data;
--   * the machine-produced concrete signed-factorial term identification;
--   * the genuine Bishop Machin real constructed from convergent arctan series.
--
-- This removes the formerly arbitrary "selected pi" source parameter from the
-- Moonshine/Eisenstein route.  The only remaining cross-assistant semantic
-- obligation is to identify this exact Bishop Machin real with classical pi.
------------------------------------------------------------------------

import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopConcreteTrigSeriesConvergenceExact as TrigConvergence
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import Sequence as BishopSequence
import Real as BishopReal

open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

round11MachinTranscendentals :
  Round11.Round11BishopCutset →
  Complex.BishopSetoidComplexTranscendentals
round11MachinTranscendentals inputs = record
  { Complex.dataSet = Round11.elementarySeries inputs
  ; Complex.trigIdentification =
      Round11.round11ConcreteTermIdentification inputs
  ; Complex.pi = Machin.bishopMachinPi
  }

round11MachinExpConverges :
  ∀ (inputs : Round11.Round11BishopCutset)
    (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Exp.expTerm point))
    (Exp.bishopExp point)
round11MachinExpConverges inputs point =
  Exp.bishopExpConverges point

round11MachinSineConverges :
  ∀ (inputs : Round11.Round11BishopCutset)
    (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
    (Elementary.bishopSin
      (Round11.elementarySeries inputs)
      point)
round11MachinSineConverges inputs =
  TrigConvergence.concreteSineSeriesConverges inputs

round11MachinCosineConverges :
  ∀ (inputs : Round11.Round11BishopCutset)
    (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.cosineSignedTerm point))
    (Elementary.bishopCos
      (Round11.elementarySeries inputs)
      point)
round11MachinCosineConverges inputs =
  TrigConvergence.concreteCosineSeriesConverges inputs

round11MachinAtanOneFifthConverges :
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Machin.atanSignedTerm Machin.bishopOneFifth))
    Machin.bishopAtanOneFifth
round11MachinAtanOneFifthConverges =
  Machin.bishopAtanHalfBallConverges
    Machin.bishopOneFifth
    Machin.bishopOneFifthInsideHalf

round11MachinAtanOneTwoHundredThirtyNinthConverges :
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Machin.atanSignedTerm
        Machin.bishopOneTwoHundredThirtyNinth))
    Machin.bishopAtanOneTwoHundredThirtyNinth
round11MachinAtanOneTwoHundredThirtyNinthConverges =
  Machin.bishopAtanHalfBallConverges
    Machin.bishopOneTwoHundredThirtyNinth
    Machin.bishopOneTwoHundredThirtyNinthInsideHalf

record Round11MachinRouteBSourceReceipt
    (inputs : Round11.Round11BishopCutset) : Set₁ where
  constructor round11-machin-route-b-source-receipt
  field
    transcendentals :
      Complex.BishopSetoidComplexTranscendentals

    transcendentalsAreRound11Machin :
      transcendentals ≡ round11MachinTranscendentals inputs

    exponentialConvergence :
      ∀ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Exp.expTerm point))
        (Exp.bishopExp point)

    sineConvergence :
      ∀ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
        (Elementary.bishopSin
          (Round11.elementarySeries inputs)
          point)

    cosineConvergence :
      ∀ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Terms.cosineSignedTerm point))
        (Elementary.bishopCos
          (Round11.elementarySeries inputs)
          point)

    atanOneFifthConvergence :
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf
          (Machin.atanSignedTerm Machin.bishopOneFifth))
        Machin.bishopAtanOneFifth

    atanOneTwoHundredThirtyNinthConvergence :
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf
          (Machin.atanSignedTerm
            Machin.bishopOneTwoHundredThirtyNinth))
        Machin.bishopAtanOneTwoHundredThirtyNinth

open Round11MachinRouteBSourceReceipt public

canonicalRound11MachinRouteBSourceReceipt :
  (inputs : Round11.Round11BishopCutset) →
  Round11MachinRouteBSourceReceipt inputs
canonicalRound11MachinRouteBSourceReceipt inputs =
  round11-machin-route-b-source-receipt
    (round11MachinTranscendentals inputs)
    refl
    (round11MachinExpConverges inputs)
    (round11MachinSineConverges inputs)
    (round11MachinCosineConverges inputs)
    round11MachinAtanOneFifthConverges
    round11MachinAtanOneTwoHundredThirtyNinthConverges

record Boundary : Set where
  constructor boundary
  field
    round11TrigSelected : Bool
    concreteTrigIdentificationSelected : Bool
    bishopMachinPiSelected : Bool
    expConvergenceOwned : Bool
    concreteSinConvergenceOwned : Bool
    concreteCosConvergenceOwned : Bool
    machinAtanOneFifthConvergenceOwned : Bool
    machinAtanOne239ConvergenceOwned : Bool

    bishopMachinPiEqualsClassicalPiProvedHere : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true true
    false

round11MachinRouteBSourceLevel : ProofLevel
round11MachinRouteBSourceLevel = machineChecked

bishopMachinPiClassicalSameObjectLevel : ProofLevel
bishopMachinPiClassicalSameObjectLevel = conditional
