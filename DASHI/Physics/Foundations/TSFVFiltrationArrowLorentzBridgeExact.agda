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
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as History
import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as Micro
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

------------------------------------------------------------------------
-- An EARLIER, stronger SAME-CARRIER finite temporal witness.
-- FiniteHistoryOrientationExact already owns the original proofs.
-- Its action is time-reversal invariant, two later boundary selections
-- retain the same recorded past, but correspond to distinct hidden
-- histories with identical action value.
-- Thus neither the action number nor a past-only observation can
-- reconstruct the selected hidden history. This is finite operational
-- asymmetry, NOT a metric-time-axis theorem.
------------------------------------------------------------------------

microscopicReversalInvolutive :
  (h : Micro.History2) →
  Micro.reverseHistory (Micro.reverseHistory h) ≡ h
microscopicReversalInvolutive = Micro.reverseHistoryInvolutive

microscopicActionTimeReversalInvariant :
  (h : Micro.History2) →
  Micro.historyAction (Micro.reverseHistory h) ≡ Micro.historyAction h
microscopicActionTimeReversalInvariant = Micro.actionTimeReversalInvariant

futureChoicesKeepSamePast :
  Micro.pastAccessibleOutcome Micro.chooseMinusBoundary ≡
  Micro.pastAccessibleOutcome Micro.choosePlusBoundary
futureChoicesKeepSamePast = Micro.finiteNoBackwardSignalling

futureChoicesChangeHiddenHistory :
  Micro.hiddenHistory Micro.chooseMinusBoundary ≡
  Micro.hiddenHistory Micro.choosePlusBoundary → ⊥
futureChoicesChangeHiddenHistory =
  Micro.futureBoundaryCanChangeHiddenHistory

futureChoicesHaveSameMicroscopicAction :
  Micro.historyAction (Micro.hiddenHistory Micro.chooseMinusBoundary) ≡
  Micro.historyAction (Micro.hiddenHistory Micro.choosePlusBoundary)
futureChoicesHaveSameMicroscopicAction = refl

-- The physical distinction is not encoded in the action value.
-- Any putative history decoder solely from that value fails on the
-- two actual source-owned hidden-history witnesses.
historyNotRecoverableFromActionAlone :
  (decode : Nat → Micro.History2) →
  (correct :
    (choice : Micro.LaterChoice) →
    decode (Micro.historyAction (Micro.hiddenHistory choice))
    ≡ Micro.hiddenHistory choice) →
  ⊥
historyNotRecoverableFromActionAlone decode correct =
  futureChoicesChangeHiddenHistory
    (trans (sym (correct Micro.chooseMinusBoundary))
      (trans (cong decode futureChoicesHaveSameMicroscopicAction)
        (correct Micro.choosePlusBoundary)))

-- The exact source-owned coarse past observation is also lossy:
-- both future choices yield the *same* recorded past, but distinct
-- underlying histories. No deterministic decoder from that one coarse
-- observation can reconstruct the true selected history in both cases.
--
-- This directly models the conjecture in dashiQ/PHYSICS_TARGETS.md:
-- reversible microscopic history + lossy observation. It is a finite
-- non-factorability theorem, not a proof of thermodynamic entropy growth
-- or an emergent Lorentzian clock.
pastRecordCannotRecoverSelectedMicroHistory :
  (recover : Micro.PastRecord → Micro.History2) →
  (correct :
    (choice : Micro.LaterChoice) →
    recover (Micro.pastAccessibleOutcome choice)
    ≡ Micro.hiddenHistory choice) →
  ⊥
pastRecordCannotRecoverSelectedMicroHistory recover correct =
  futureChoicesChangeHiddenHistory
    (trans (sym (correct Micro.chooseMinusBoundary))
      (trans (cong recover futureChoicesKeepSamePast)
        (correct Micro.choosePlusBoundary)))

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
