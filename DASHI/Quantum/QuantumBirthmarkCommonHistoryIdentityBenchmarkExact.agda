{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkCommonHistoryIdentityBenchmarkExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History

------------------------------------------------------------------------
-- CANONICAL FINITE SAME-CARRIER BENCHMARK
--
-- This closes constructive inhabitance of the history->common-history adapter
-- on the repo's finite-history carrier.  It is not a claim that the physical
-- continuum/CMP119 history carrier is definitionally this finite carrier.
------------------------------------------------------------------------

data BirthmarkClass : Set where
  lowBirthmark : BirthmarkClass
  highBirthmark : BirthmarkClass

selectedHistory : BirthmarkClass → History.History3
selectedHistory lowBirthmark = History.historyABC
selectedHistory highBirthmark = History.historyACB

identityHistoryMap : History.History3 → History.History3
identityHistoryMap history = history

selectedBirthmarkHistoryMapsByRefl :
  (birthmark : BirthmarkClass) →
  identityHistoryMap (selectedHistory birthmark) ≡ selectedHistory birthmark
selectedBirthmarkHistoryMapsByRefl birthmark = refl

lowBirthmarkMapsToHistoryABC :
  identityHistoryMap (selectedHistory lowBirthmark) ≡ History.historyABC
lowBirthmarkMapsToHistoryABC = refl

highBirthmarkMapsToHistoryACB :
  identityHistoryMap (selectedHistory highBirthmark) ≡ History.historyACB
highBirthmarkMapsToHistoryACB = refl

commonHistoryMapBenchmarkOwned : Bool
commonHistoryMapBenchmarkOwned = true

finiteSameCarrierInhabitationOwned : Bool
finiteSameCarrierInhabitationOwned = true

physicalCMP119HistoryCarrierIdentifiedByThisBenchmark : Bool
physicalCMP119HistoryCarrierIdentifiedByThisBenchmark = false

physicalHistoryMapStillSourceSpecific : Bool
physicalHistoryMapStillSourceSpecific = true
