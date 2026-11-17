module DASHI.Analysis.PickoverAnalyticJHistoricalPhaseConsumerExact where

------------------------------------------------------------------------
-- PICKOVER x ANALYTICAL J: ACTUAL BISHOP SINE PHASE READOUT.
--
-- Existing source owners (import, don't copy):
-- JInvariantBishopTrigUnitPhaseExact: genuine Bishop cos(theta)+i sin(theta)
-- JInvariantBishopQFromUnitPhaseExact: unit-phase-to-q radial envelope
-- JInvariantAnalyticJCoarseFineObserverExact: finite analytic j observer
-- JInvariant369LevelNonDescentThroughJExact: T-invariant j loses lift
-- PickoverConsumerResidualFibreBridgeExact: consumer-indexed necessity
-- WaveAlgorithmLift: wave evolution and refinement obligations
-- HistoryTimeIndexedConsumerFibreExact: indexed history/consumer closure.
--
-- Mathematical roots: Machin (1706), Bishop/Bridges constructive
-- analysis (1985), Murray (2022), classical Euler/de Moivre.
--
-- This makes the exact analytic carrier/consumer connection:
-- imaginary(bishopTrigPhase(theta)) DEFINITIONALLY is bishopSin(theta).
-- It does not falsely equate modular j-values, finite C3 phase labels
-- or a q-series convergence bound with a sign certificate for 9999!.
-- Constructing the actual giant Bishop real theta and its separated
-- positive/negative interval is a distinct executable obligation.
--
-- Source-written, Agda kernel pending; no ESD edits or claims about
-- Monster 3B, twin primes, or terminal Pickover sign.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Real as BishopReal
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Moonshine.JInvariantBishopTrigUnitPhaseExact as TrigJ
import DASHI.Moonshine.JInvariantBishopQFromUnitPhaseExact as RadialJ
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as JObserver
import DASHI.Moonshine.JInvariant369LevelNonDescentThroughJExact as JNonDescent
import DASHI.Analysis.PickoverConsumerResidualFibreBridgeExact as Pickover
import DASHI.Physics.WaveAlgorithmLift as Wave
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as History

-- This is the TRUE sine series on the original Bishop analytic phase.
-- A C3 / 101 / Eisenstein / modular-j finite chart cannot replace it.
realSineReadout :
  Elementary.BishopElementaryPowerSeriesData ->
  BishopReal.ℝ -> BishopReal.ℝ
realSineReadout dataSet angle =
  Complex.im (TrigJ.bishopTrigPhase dataSet angle)

realSineReadoutIsActualBishopSin :
  (dataSet : Elementary.BishopElementaryPowerSeriesData)
  (angle : BishopReal.ℝ) ->
  realSineReadout dataSet angle
    ≡ Elementary.bishopSin dataSet angle
realSineReadoutIsActualBishopSin dataSet angle = refl

-- Consumer-sufficiency of the actual analytic phase *with its
-- imaginary coordinate retained*. This is an EXACT equality theorem,
-- no numerical sign decision. It follows from the original phase
-- producer, not from a synthetic finite torque/SSP table.
actualTrigPhaseObserver :
  Elementary.BishopElementaryPowerSeriesData ->
  BishopReal.ℝ -> Complex.BishopComplex
actualTrigPhaseObserver = TrigJ.bishopTrigPhase

actualPhaseEqualityDeterminesSine :
  (dataSet : Elementary.BishopElementaryPowerSeriesData)
  (left right : BishopReal.ℝ) ->
  actualTrigPhaseObserver dataSet left
    ≡ actualTrigPhaseObserver dataSet right ->
  Elementary.bishopSin dataSet left
    ≡ Elementary.bishopSin dataSet right
actualPhaseEqualityDeterminesSine dataSet left right same =
  trans
    (sym (realSineReadoutIsActualBishopSin dataSet left))
    (trans
      (cong Complex.im same)
      (realSineReadoutIsActualBishopSin dataSet right))

-- Actual history-aware phase readout can be recovered at terminal
-- time from the RETAINED last phase, rather than a finite modular
-- invariant. Do not assert any finite j or q label is sufficient.
record RetainedBishopPhaseHistory
    (dataSet : Elementary.BishopElementaryPowerSeriesData) : Set where
  constructor retained-bishop-phase-history
  field
    priorPhase : Complex.BishopComplex
    livePhase : Complex.BishopComplex
    terminalPhase : Complex.BishopComplex

open RetainedBishopPhaseHistory public

terminalSignedReal :
  (dataSet : Elementary.BishopElementaryPowerSeriesData) ->
  RetainedBishopPhaseHistory dataSet -> BishopReal.ℝ
terminalSignedReal dataSet history =
  Complex.im (terminalPhase history)

terminalHistoryConsumerRecovery :
  (dataSet : Elementary.BishopElementaryPowerSeriesData) ->
  (left right : RetainedBishopPhaseHistory dataSet) ->
  terminalPhase left ≡ terminalPhase right ->
  terminalSignedReal dataSet left
    ≡ terminalSignedReal dataSet right
terminalHistoryConsumerRecovery dataSet left right same =
  cong Complex.im same

-- Construct a sound end-to-end real phase history at a supplied
-- actual angle. This is the RIGHT obligation for Pickover: an
-- analytic witness of terminalPhase = cos(theta)+i sin(theta).
record ActualAnalyticTerminalPhase
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (angle : BishopReal.ℝ) : Set where
  field
    history : RetainedBishopPhaseHistory dataSet
    terminalIsTrueTrig :
      terminalPhase history ≡ TrigJ.bishopTrigPhase dataSet angle

open ActualAnalyticTerminalPhase public

analyticJHistorySineExact :
  (dataSet : Elementary.BishopElementaryPowerSeriesData)
  (angle : BishopReal.ℝ)
  (cert : ActualAnalyticTerminalPhase dataSet angle) ->
  terminalSignedReal dataSet (history cert)
    ≡ Elementary.bishopSin dataSet angle
analyticJHistorySineExact dataSet angle cert =
  trans
    (cong Complex.im (terminalIsTrueTrig cert))
    (realSineReadoutIsActualBishopSin dataSet angle)

-- A proof that an enclosure for the retained imaginary part lies on
-- a strictly positive or negative side needs the REAL ORDER and
-- corresponding certified bound. Those are intentionally NOT
-- invented or replaced with modular j / q observations.
