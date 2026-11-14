module DASHI.Cognition.PNF.EnactedTemporalOrderRegression where

-- Source: Jeremy Rodgers (2026-10-23),
-- Experienced Temporal Passage: Enacted Scaffolding and the Organization
-- of Succession, DOI 10.5281/zenodo.23591626, propositions 1 and 5.
-- These are DASHI finite-model regressions, not proof of the paper's
-- constitutive identity or an actually experiencing human/circuit.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.EnactedTemporalOrderExact as Temporal

chosenPrefix : List Nat
chosenPrefix = 1 ∷ 2 ∷ []

laterSequenceA : List Nat
laterSequenceA = 42 ∷ []

laterSequenceB : List Nat
laterSequenceB = 99 ∷ []

-- One source prefix and two differing suffixes produce the same
-- prefix-indexed current state, regardless of the rest of each future.
sameCurrentStateForDifferentFuture :
  Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (Temporal._++_ chosenPrefix laterSequenceA))
  ≡
  Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (Temporal._++_ chosenPrefix laterSequenceB))
sameCurrentStateForDifferentFuture =
  Temporal.equalReceivedPrefixesGiveEqualOnlineStates
    _+_ zero chosenPrefix laterSequenceA laterSequenceB

sameCurrentObservationForDifferentFuture :
  suc (Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (Temporal._++_ chosenPrefix laterSequenceA)))
  ≡
  suc (Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (Temporal._++_ chosenPrefix laterSequenceB)))
sameCurrentObservationForDifferentFuture =
  Temporal.equalReceivedPrefixesGiveEqualObservedOutputs
    _+_ suc zero chosenPrefix laterSequenceA laterSequenceB

arrivingEPrecedesArrivingC : (Temporal._earlier?_ Temporal.receivedE Temporal.receivedC) ≡
  true
arrivingEPrecedesArrivingC = Temporal.receptionEC

sourceCPrecedesSourceE : (Temporal._earlier?_ Temporal.sourceC Temporal.sourceE) ≡
  true
sourceCPrecedesSourceE = Temporal.sourceCE


-- Consumer-relative refinement:
-- receiver C@80/E@60 alone cannot distinguish the two source orders,
-- while independently known exact delay profiles separate THIS finite pair.
sourceOrdersCollideAtReceiver :
  Temporal.observedArrivals Temporal.cSourceFirstWithCrossingDelay ≡
  Temporal.observedArrivals Temporal.eSourceFirstWithOtherDelay
sourceOrdersCollideAtReceiver =
  Temporal.twoSourcesSameLabelledArrival

sourceOrderWithFirstCalibration :
  Temporal.readSourceOrderWithCalibration
    (Temporal.calibratedObserver
      Temporal.cSourceFirstWithCrossingDelay)
    ≡ Temporal.sourceCFirst
sourceOrderWithFirstCalibration = refl

sourceOrderWithSecondCalibration :
  Temporal.readSourceOrderWithCalibration
    (Temporal.calibratedObserver
      Temporal.eSourceFirstWithOtherDelay)
    ≡ Temporal.sourceEFirst
sourceOrderWithSecondCalibration = refl

-- The synthetic delays really compose to the identical receiver readings.
secondWorldCArrives80 :
  50 + 30 ≡ 80
secondWorldCArrives80 = Temporal.secondWorldCArrival
