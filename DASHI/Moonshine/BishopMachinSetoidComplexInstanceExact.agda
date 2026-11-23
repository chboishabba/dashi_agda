module DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact where

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
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import Sequence as BishopSequence
import Real as BishopReal

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

machinTranscendentals :
  Round11.BishopCutset →
  Complex.BishopSetoidComplexTranscendentals
machinTranscendentals inputs = record
  { Complex.dataSet = Round11.elementarySeries inputs
  ; Complex.trigIdentification =
      Round11.concreteTermIdentification inputs
  ; Complex.pi = Machin.bishopMachinPi
  }

machinExpConverges :
  ∀ (inputs : Round11.BishopCutset)
    (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Exp.expTerm point))
    (Exp.bishopExp point)
machinExpConverges inputs point =
  Exp.bishopExpConverges point

machinSineConverges :
  ∀ (inputs : Round11.BishopCutset)
    (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
    (Elementary.bishopSin
      (Round11.elementarySeries inputs)
      point)
machinSineConverges inputs =
  TrigConvergence.concreteSineSeriesConverges inputs

machinCosineConverges :
  ∀ (inputs : Round11.BishopCutset)
    (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.cosineSignedTerm point))
    (Elementary.bishopCos
      (Round11.elementarySeries inputs)
      point)
machinCosineConverges inputs =
  TrigConvergence.concreteCosineSeriesConverges inputs

machinAtanOneFifthConverges :
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Machin.atanSignedTerm Machin.bishopOneFifth))
    Machin.bishopAtanOneFifth
machinAtanOneFifthConverges =
  Machin.bishopAtanHalfBallConverges
    Machin.bishopOneFifth
    Machin.bishopOneFifthInsideHalf

machinAtanOneTwoHundredThirtyNinthConverges :
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Machin.atanSignedTerm
        Machin.bishopOneTwoHundredThirtyNinth))
    Machin.bishopAtanOneTwoHundredThirtyNinth
machinAtanOneTwoHundredThirtyNinthConverges =
  Machin.bishopAtanHalfBallConverges
    Machin.bishopOneTwoHundredThirtyNinth
    Machin.bishopOneTwoHundredThirtyNinthInsideHalf

record MachinRouteBSourceReceipt
    (inputs : Round11.BishopCutset) : Set₁ where
  constructor round11-machin-route-b-source-receipt
  field
    transcendentals :
      Complex.BishopSetoidComplexTranscendentals

    transcendentalsAreRound11Machin :
      transcendentals ≡ machinTranscendentals inputs

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

open MachinRouteBSourceReceipt public

canonicalMachinRouteBSourceReceipt :
  (inputs : Round11.BishopCutset) →
  MachinRouteBSourceReceipt inputs
canonicalMachinRouteBSourceReceipt inputs =
  round11-machin-route-b-source-receipt
    (machinTranscendentals inputs)
    refl
    (machinExpConverges inputs)
    (machinSineConverges inputs)
    (machinCosineConverges inputs)
    machinAtanOneFifthConverges
    machinAtanOneTwoHundredThirtyNinthConverges

record Boundary : Set where
  constructor boundary
  field
    trigSelected : Bool
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

machinRouteBSourceLevel : ProofLevel
machinRouteBSourceLevel = machineChecked

bishopMachinPiClassicalSameObjectLevel : ProofLevel
bishopMachinPiClassicalSameObjectLevel = conditional
