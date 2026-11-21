{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVObservedPhysicalAccessTransportExact where

------------------------------------------------------------------------
-- P01 -> P02: THE ORIGINAL OBSERVER'S ACCESS ORDER AT THE SAME STATE.
--
-- Existing TSFVFiltrationArrowLorentzBridgeExact carries the explicit
-- physical source identification:
--
--   observedFiltration selectedState level event
--     = ORIGINAL HistoryWeightFiltrationExact.visibleAt level event.
--
-- Previously the conditional (3,1) theorem consumed only the selected
-- arrow-axis Boolean probe. Here the ORIGINAL source access preorder is
-- transported both ways at that SAME selected state, with its strict
-- intermediate/terminal event witnesses. No substitute observer order
-- or independently assigned "time" tag is introduced.
--
-- This is an exact source-indexed implication for any ACTUALLY inhabited
-- SelectedTSFVToLorentzPhysicalSource. It does NOT inhabit that record
-- or derive a spacetime signal cone, metric, dimension or physical
-- generator from finite record accessibility.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as History
import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as Bridge
import DASHI.Physics.Foundations.TSFVOriginalObserverVisibilityCausalOrderExact as Access

-- Actual access monotonicity on the VERY SAME physical observer state
-- selected by the original conditional Lorentz source owner.
SelectedObservedAccessOrder :
  Bridge.SelectedTSFVToLorentzPhysicalSource →
  History.FiltrationLevel → History.FiltrationLevel → Set
SelectedObservedAccessOrder selected early late =
  (event : History.Event) →
  Bridge.SelectedTSFVToLorentzPhysicalSource.observedFiltration selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    early event ≡ true →
  Bridge.SelectedTSFVToLorentzPhysicalSource.observedFiltration selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    late event ≡ true

-- The SOURCE OWNERS' existing pointwise identity transports both
-- original and observed order, with no new source/mapping hypothesis.
originalAccessImpliesActualMeasuredAccess :
  (selected : Bridge.SelectedTSFVToLorentzPhysicalSource)
  (early late : History.FiltrationLevel) →
  Access._⊑obs_ early late →
  SelectedObservedAccessOrder selected early late
originalAccessImpliesActualMeasuredAccess
    selected early late original event visible =
  trans
    (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
      selected late event)
    (original event
      (trans
        (sym
          (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
            selected early event))
        visible))

actualMeasuredAccessImpliesOriginal :
  (selected : Bridge.SelectedTSFVToLorentzPhysicalSource)
  (early late : History.FiltrationLevel) →
  SelectedObservedAccessOrder selected early late →
  Access._⊑obs_ early late
actualMeasuredAccessImpliesOriginal
    selected early late measured event originalVisible =
  trans
    (sym
      (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
        selected late event))
    (measured event
      (trans
        (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
          selected early event)
        originalVisible))

sameSelectedObserverAccessIFFOriginal :
  (selected : Bridge.SelectedTSFVToLorentzPhysicalSource)
  (early late : History.FiltrationLevel) →
  (Access._⊑obs_ early late →
    SelectedObservedAccessOrder selected early late)
  ×
  (SelectedObservedAccessOrder selected early late →
    Access._⊑obs_ early late)
sameSelectedObserverAccessIFFOriginal selected early late =
  originalAccessImpliesActualMeasuredAccess selected early late ,
  actualMeasuredAccessImpliesOriginal selected early late

-- Selected original event accessibility has independent middle/late
-- strict gain on that exact physical state, not on another observer.
measuredMiddleEventStrictGain :
  (selected : Bridge.SelectedTSFVToLorentzPhysicalSource) →
  Bridge.SelectedTSFVToLorentzPhysicalSource.observedFiltration selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    History.initialFiltration History.intermediateEvent ≡ false
  ×
  Bridge.SelectedTSFVToLorentzPhysicalSource.observedFiltration selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    History.intermediateFiltration History.intermediateEvent ≡ true
measuredMiddleEventStrictGain selected =
  trans
    (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
      selected History.initialFiltration History.intermediateEvent)
    refl ,
  trans
    (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
      selected History.intermediateFiltration History.intermediateEvent)
    refl

measuredTerminalEventStrictGain :
  (selected : Bridge.SelectedTSFVToLorentzPhysicalSource) →
  Bridge.SelectedTSFVToLorentzPhysicalSource.observedFiltration selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    History.intermediateFiltration History.terminalEvent ≡ false
  ×
  Bridge.SelectedTSFVToLorentzPhysicalSource.observedFiltration selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    History.terminalFiltration History.terminalEvent ≡ true
measuredTerminalEventStrictGain selected =
  trans
    (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
      selected History.intermediateFiltration History.terminalEvent)
    refl ,
  trans
    (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
      selected History.terminalFiltration History.terminalEvent)
    refl

-- The selected physical probe on the EXISTING selected measured axis
-- sees the same terminal visibility fact. This follows from the
-- original selected-arrow-matches-observation assumption; not from
-- the finite filter alone, so the physical producer remains explicit.
originalTerminalVisibleOnMeasuredArrowAxis :
  (selected : Bridge.SelectedTSFVToLorentzPhysicalSource) →
  Bridge.SelectedTSFVToLorentzPhysicalSource.measuredPrincipalAxisProbe
    selected
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedState selected)
    (Bridge.SelectedTSFVToLorentzPhysicalSource.measuredArrowAxis selected)
  ≡ true
originalTerminalVisibleOnMeasuredArrowAxis selected =
  trans
    (Bridge.SelectedTSFVToLorentzPhysicalSource.selectedArrowMatchesLateObservation
      selected)
    (trans
      (Bridge.SelectedTSFVToLorentzPhysicalSource.filtrationIsSameSource
        selected History.terminalFiltration History.terminalEvent)
      refl)

-- The terminal-signal readout and operational access order are now
-- on the SAME conditional physical source, but proving that source's
-- observer clock is the principal propagation cone remains P02 OPEN.
