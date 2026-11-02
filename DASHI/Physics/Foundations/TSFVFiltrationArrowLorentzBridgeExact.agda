{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact where

-- Reuse original two-boundary / observer-filtration theorem owners.
-- Original TSVF: Aharonov, Bergmann & Lebowitz (1964);
-- subsequent two-state-vector formalism: Aharonov & Vaidman.
-- DASHI's earlier two-boundary Agda owner: PR #84.
-- The finite history/filter/action owners remain separately attributed.
--
-- Here the constructed filtration distinguishes early from late
-- information access. This is an OPERATIONAL information arrow.
-- It is NOT itself a temporal metric principal axis, a proof of 3+1
-- emergence, or controllable backwards signalling.
-- Physical source-identification stays an explicit proof input.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as History
import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as Lorentz

earlyObserverCannotSeeFinal :
  History.visibleAt History.initialFiltration History.terminalEvent ≡ false
earlyObserverCannotSeeFinal =
  History.initialObserverCannotAccessTerminalEvent

lateObserverCanSeeFinal :
  History.visibleAt History.terminalFiltration History.terminalEvent ≡ true
lateObserverCanSeeFinal = refl

-- No numerical signature tag occurs in this derived contrast.
earlyAndLateVisibilityDiffer :
  History.visibleAt History.initialFiltration History.terminalEvent ≡
  History.visibleAt History.terminalFiltration History.terminalEvent → ⊥
earlyAndLateVisibilityDiffer ()

-- Same future-conditioned observation can affect smoothing/retrodiction.
-- This existing theorem does NOT imply that a later intervention
-- changes an already registered past event.
futureBoundaryChangesSmoothing :
  History.smoothEstimate History.leftBoundary ≡
  History.smoothEstimate History.rightBoundary → ⊥
futureBoundaryChangesSmoothing =
  History.smoothingCanDependOnFutureBoundary

-- The exact physical promotion boundary. The observer's source is
-- explicitly the SAME selected state; the measured arrow must be
-- calibrated to the signs of the same actual quadratic.
record SelectedTSFVToLorentzPhysicalSource : Set₁ where
  field
    PhysicalState : Set
    selectedState : PhysicalState

    observedFiltration : PhysicalState →
      History.FiltrationLevel → History.Event → Bool

    filtrationIsSameSource :
      (level : History.FiltrationLevel) (event : History.Event) →
      observedFiltration selectedState level event ≡
      History.visibleAt level event

    measuredPrincipalAxisProbe :
      PhysicalState → Lorentz.Axis → Bool

    physicalQuadraticAxisSigns :
      PhysicalState → Lorentz.Axis → Lorentz.AxisSign

    measuredArrowAxis : Lorentz.Axis

    -- Physical content: which direction in the SAME measured metric
    -- corresponds to the observer-information asymmetry. No inhabitant
    -- is constructed here from just the labels initial/final.
    selectedArrowMatchesLateObservation :
      measuredPrincipalAxisProbe selectedState measuredArrowAxis ≡
      observedFiltration selectedState
        History.terminalFiltration History.terminalEvent

    selectedArrowFailsEarlyObservation :
      observedFiltration selectedState
        History.initialFiltration History.terminalEvent ≡ false

    uniqueMeasuredArrow :
      Lorentz.DirectionalProbe (measuredPrincipalAxisProbe selectedState)

    calibratedQuadratic :
      Lorentz.AxisCalibration
        (measuredPrincipalAxisProbe selectedState)
        (physicalQuadraticAxisSigns selectedState)

-- Conditional on the genuinely physical source-to-axis bridge above.
-- In particular the filtration theorem alone cannot inhabit the record.
selectedTSFVPhysicalSignatureIs31 :
  (w : SelectedTSFVToLorentzPhysicalSource) →
  Lorentz.actualAxisCounts
    (SelectedTSFVToLorentzPhysicalSource.physicalQuadraticAxisSigns w
      (SelectedTSFVToLorentzPhysicalSource.selectedState w))
  ≡ Lorentz.signature 3 1
selectedTSFVPhysicalSignatureIs31 w =
  Lorentz.calibratedProbeForcesThreePlusOne
    (SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow w)
    (SelectedTSFVToLorentzPhysicalSource.calibratedQuadratic w)
