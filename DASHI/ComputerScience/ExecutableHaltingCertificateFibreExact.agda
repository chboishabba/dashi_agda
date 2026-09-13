module DASHI.ComputerScience.ExecutableHaltingCertificateFibreExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid

------------------------------------------------------------------------
-- EXECUTABLE HALTING CERTIFICATES OVER THE ACTUAL RADIX-NEUTRAL MACHINE
--
-- Positive halting is witnessed by a concrete finite fuel bound together with
-- an exact proof that the resulting state is halted.  By contrast, observing
-- that a computation has not halted within some finite fuel does not prove
-- non-halting.  This module is deliberately a bounded/executable surface; it
-- does not claim a formal proof of Turing's undecidability theorem.
------------------------------------------------------------------------

record HaltingCertificate (start : Machine.MachineState) : Set where
  constructor haltingCertificate
  field
    fuel : Nat
    terminal : Machine.MachineState
    terminalIsRun : terminal ≡ Machine.runFuel fuel start
    terminalIsHalted : Machine.halted terminal ≡ true

open HaltingCertificate public

record BoundedNonHaltingObservation (start : Machine.MachineState) : Set where
  constructor boundedNonHaltingObservation
  field
    fuelObserved : Nat
    observedState : Machine.MachineState
    observedStateIsRun : observedState ≡ Machine.runFuel fuelObserved start
    observedNotHalted : Machine.halted observedState ≡ false

open BoundedNonHaltingObservation public

------------------------------------------------------------------------
-- Concrete positive certificate: the existing 48,18 Euclid execution.
------------------------------------------------------------------------

euclid4818HaltingCertificate :
  HaltingCertificate (Euclid.euclidInitialState 48 18)
euclid4818HaltingCertificate =
  haltingCertificate
    Euclid.euclid4818Fuel
    Euclid.euclid4818Final
    refl
    Euclid.euclid4818Halts

------------------------------------------------------------------------
-- Concrete bounded negative observation on the same computation.
-- After zero fuel the initial state is visibly not halted, but this says
-- nothing about whether it eventually halts.  The positive certificate above
-- demonstrates the distinction on one literal same-object computation.
------------------------------------------------------------------------

euclid4818InitiallyNotHalted :
  BoundedNonHaltingObservation (Euclid.euclidInitialState 48 18)
euclid4818InitiallyNotHalted =
  boundedNonHaltingObservation
    0
    (Euclid.euclidInitialState 48 18)
    refl
    refl

------------------------------------------------------------------------
-- Semantic-property observer.  A property of a bounded terminal observation
-- is distinct from the syntactic program and from a generic decision procedure
-- for that property over all programs.
------------------------------------------------------------------------

record BoundedSemanticProperty : Set₁ where
  constructor boundedSemanticProperty
  field
    Property : Set
    observe : Machine.MachineState → Property

open BoundedSemanticProperty public

haltedObserver : BoundedSemanticProperty
haltedObserver = boundedSemanticProperty Bool Machine.halted

outputObserver : BoundedSemanticProperty
outputObserver = boundedSemanticProperty (List Nat) Machine.output

pcObserver : BoundedSemanticProperty
pcObserver = boundedSemanticProperty Nat Machine.pc

------------------------------------------------------------------------
-- Firewalls: these empty types make the bounded/infinite distinction explicit.
------------------------------------------------------------------------

data BoundedNonHaltingObservationIsNonHaltingProof : Set where
data HaltingCertificateIsGeneralHaltingDecider : Set where
data BoundedSemanticObserverIsRiceTheorem : Set where
data ConcreteLongRuntimeIsBusyBeaverTheorem : Set where

boundedObservationDoesNotBecomeNonHaltingProof :
  BoundedNonHaltingObservationIsNonHaltingProof → ⊥
boundedObservationDoesNotBecomeNonHaltingProof ()

haltingWitnessDoesNotCreateGeneralDecider :
  HaltingCertificateIsGeneralHaltingDecider → ⊥
haltingWitnessDoesNotCreateGeneralDecider ()

semanticObserverDoesNotByItselfProveRice :
  BoundedSemanticObserverIsRiceTheorem → ⊥
semanticObserverDoesNotByItselfProveRice ()

longRuntimeDoesNotByItselfProveBusyBeaver :
  ConcreteLongRuntimeIsBusyBeaverTheorem → ⊥
longRuntimeDoesNotByItselfProveBusyBeaver ()

record ExecutableHaltingBoundary : Set where
  constructor executableHaltingBoundary
  field
    positiveHaltingCertificateExecutable : Bool
    boundedNegativeObservationExecutable : Bool
    finiteNonHaltingObservationPromotedToNonHaltingProof : Bool
    generalHaltingDeciderClaimed : Bool
    riceTheoremClaimedFromSemanticObserverAlone : Bool
    busyBeaverTheoremClaimedFromConcreteRuntimeAlone : Bool

canonicalExecutableHaltingBoundary : ExecutableHaltingBoundary
canonicalExecutableHaltingBoundary =
  executableHaltingBoundary true true false false false false
