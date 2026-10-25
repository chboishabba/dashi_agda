module DASHI.Cognition.PNF.EnactedTemporalOrderRegression where

-- Source: Jeremy Rodgers (2026-10-23),
-- Experienced Temporal Passage: Enacted Scaffolding and the Organization
-- of Succession, DOI 10.5281/zenodo.23591626, propositions 1 and 5.
-- These are DASHI finite-model regressions, not proof of the paper's
-- constitutive identity or an actually experiencing human/circuit.

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
      (chosenPrefix Temporal.++ laterSequenceA))
  ≡
  Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (chosenPrefix Temporal.++ laterSequenceB))
sameCurrentStateForDifferentFuture =
  Temporal.equalReceivedPrefixesGiveEqualOnlineStates
    _+_ zero chosenPrefix laterSequenceA laterSequenceB

sameCurrentObservationForDifferentFuture :
  suc (Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (chosenPrefix Temporal.++ laterSequenceA)))
  ≡
  suc (Temporal.runPrefix _+_ zero
    (Temporal.prefixOfLength
      (Temporal.listLength chosenPrefix)
      (chosenPrefix Temporal.++ laterSequenceB)))
sameCurrentObservationForDifferentFuture =
  Temporal.equalReceivedPrefixesGiveEqualObservedOutputs
    _+_ suc zero chosenPrefix laterSequenceA laterSequenceB

arrivingEPrecedesArrivingC : (Temporal.receivedE Temporal.earlier? Temporal.receivedC) ≡
  Agda.Builtin.Bool.true
arrivingEPrecedesArrivingC = Temporal.receptionEC

sourceCPrecedesSourceE : (Temporal.sourceC Temporal.earlier? Temporal.sourceE) ≡
  Agda.Builtin.Bool.true
sourceCPrecedesSourceE = Temporal.sourceCE
