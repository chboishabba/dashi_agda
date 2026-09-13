module DASHI.ComputerScience.IsabelleAFPBusyBeaverAdapterTargetExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.UniversalComputabilityExternalResultExact as Universal

------------------------------------------------------------------------
-- ISABELLE/AFP BUSY BEAVER PAYMENT TARGET
--
-- The 2026 AFP development owns an external machine model and machine-checked
-- results.  This record is the exact local payment target; source observation
-- alone does not inhabit it.
------------------------------------------------------------------------

record IsabelleAFPBusyBeaverPayment : Set₁ where
  constructor isabelleAFPBusyBeaverPayment
  field
    payment : Universal.UniversalComputabilityPayment
    pinnedAFPRevision : String
    pinnedIsabelleRevision : String
    busyBeaverBaseTheoryObserved : Bool
    turingBusyBeaverTheoryObserved : Bool
    busyBeaverTheoryObserved : Bool
    universalTuringMachineDependencyObserved : Bool
    upperBoundDecidesHaltingTheoremObserved : Bool
    programInputPairHaltingResultObserved : Bool

open IsabelleAFPBusyBeaverPayment public

------------------------------------------------------------------------
-- Once the payment exists, both theorem consumers are projections; they are
-- not rebuilt separately.
------------------------------------------------------------------------

isabelleHaltingUndecidability :
  (P : IsabelleAFPBusyBeaverPayment) →
  Universal.UniversalHaltingUndecidabilityResult
    (Universal.source (payment P))
isabelleHaltingUndecidability P =
  Universal.haltingUndecidability (payment P)

isabelleBusyBeaverUpperBound :
  (P : IsabelleAFPBusyBeaverPayment) →
  Universal.BusyBeaverUpperBoundPrinciple
    (Universal.source (payment P))
isabelleBusyBeaverUpperBound P =
  Universal.busyBeaverUpperBound (payment P)

------------------------------------------------------------------------
-- Current boundary.
------------------------------------------------------------------------

record IsabelleAFPBusyBeaverBoundary : Set where
  constructor isabelleAFPBusyBeaverBoundary
  field
    externalResultLocated : Bool
    exactPaymentTargetOwned : Bool
    externalSourceSameAsDASHITinyMachine : Bool
    localPaymentInhabitantOwned : Bool
    localKernelReplayObserved : Bool

canonicalIsabelleAFPBusyBeaverBoundary : IsabelleAFPBusyBeaverBoundary
canonicalIsabelleAFPBusyBeaverBoundary =
  isabelleAFPBusyBeaverBoundary true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AFPTheoremObservationInhabitsPayment : Set where
data AFPUniversalMachineMakesTinyISAUniversal : Set where

observationDoesNotInhabitPayment : AFPTheoremObservationInhabitsPayment → ⊥
observationDoesNotInhabitPayment ()

afpUniversalityDoesNotTransferToTinyISA : AFPUniversalMachineMakesTinyISAUniversal → ⊥
afpUniversalityDoesNotTransferToTinyISA ()
