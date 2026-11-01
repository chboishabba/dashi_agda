module DASHI.Mathematics.Complexity.GenericFiniteRunTableauExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Stephen A. Cook,
-- "The complexity of theorem-proving procedures",
-- Proceedings of STOC 1971, 151--158.
-- DOI: 10.1145/800157.805047.
--
-- DASHI CONTRIBUTION
--
-- Generalise the fixed three-row Cook--Levin seed to every finite
-- nondeterministic run.  An n-step run certificate determines an (n+1)-row
-- tableau.  Its local transition constraints are exactly the successor
-- witnesses along the path, so there are n local constraints.  The
-- construction is reversible and preserves the start, finish and step count.
--
-- This closes the finite run-to-tableau layer.  Boolean cell variables,
-- exactly-one-symbol clauses, fixed-width transition windows, CNF conversion
-- and polynomial bit-size remain the next generic Cook--Levin obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.MachineRunCertificateExact as Run

prependStart : ∀ {A : Set} → A → List A → List A
prependStart start path = start ∷ path

record FiniteRunTableau
    (machine : Machine.NondeterministicMachine)
    (steps : Nat)
    (start finish : Machine.nConfiguration machine) : Set where
  constructor finiteRunTableau
  field
    successorRows : List (Machine.nConfiguration machine)
    successorRowCount : Run.listLength successorRows ≡ steps
    localTransitionConstraints :
      Run.ValidRunPath machine start successorRows finish

open FiniteRunTableau public

tableauRows :
  ∀ {machine steps start finish} →
  FiniteRunTableau machine steps start finish →
  List (Machine.nConfiguration machine)
tableauRows {start = start} tableau =
  prependStart start (successorRows tableau)

tableauRowCount :
  ∀ {machine steps start finish}
    (tableau : FiniteRunTableau machine steps start finish) →
  Run.listLength (tableauRows tableau) ≡ suc steps
tableauRowCount (finiteRunTableau rows rowCount constraints) =
  Run.congruenceSuc rowCount

localConstraintCount :
  ∀ {machine start rows finish} →
  Run.ValidRunPath machine start rows finish → Nat
localConstraintCount Run.pathDone = zero
localConstraintCount (Run.pathStep membership remainder) =
  suc (localConstraintCount remainder)

localConstraintCountEqualsPathLength :
  ∀ {machine start rows finish}
    (constraints : Run.ValidRunPath machine start rows finish) →
  localConstraintCount constraints ≡ Run.listLength rows
localConstraintCountEqualsPathLength Run.pathDone = refl
localConstraintCountEqualsPathLength (Run.pathStep membership remainder) =
  Run.congruenceSuc (localConstraintCountEqualsPathLength remainder)

localConstraintCountEqualsSteps :
  ∀ {machine steps start finish}
    (tableau : FiniteRunTableau machine steps start finish) →
  localConstraintCount (localTransitionConstraints tableau) ≡ steps
localConstraintCountEqualsSteps
    (finiteRunTableau rows refl constraints) =
  localConstraintCountEqualsPathLength constraints

runCertificateToTableau :
  ∀ {machine steps start finish} →
  Run.RunCertificate machine steps start finish →
  FiniteRunTableau machine steps start finish
runCertificateToTableau
    (Run.runCertificate path pathLength validity) =
  finiteRunTableau path pathLength validity

tableauToRunCertificate :
  ∀ {machine steps start finish} →
  FiniteRunTableau machine steps start finish →
  Run.RunCertificate machine steps start finish
tableauToRunCertificate
    (finiteRunTableau rows rowCount constraints) =
  Run.runCertificate rows rowCount constraints

runToTableauToReachability :
  ∀ {machine steps start finish} →
  Machine.NDReach machine steps start finish →
  Machine.NDReach machine steps start finish
runToTableauToReachability reachability =
  Run.certificateToReachability
    (tableauToRunCertificate
      (runCertificateToTableau
        (Run.reachabilityToCertificate reachability)))

record AcceptingTableauCertificate
    (machine : Machine.NondeterministicMachine)
    (input : Machine.nInput machine)
    (bound : Nat) : Set₁ where
  constructor acceptingTableauCertificate
  field
    steps : Nat
    withinBound : Data.Nat.Base._≤_ steps bound
    finish : Machine.nConfiguration machine
    tableau : FiniteRunTableau machine steps
      (Machine.nInitial machine input) finish
    accepting : Machine.nAccepting machine finish

open AcceptingTableauCertificate public

boundedAcceptanceToAcceptingTableau :
  ∀ machine input bound →
  Machine.NondeterministicAcceptsWithin machine input bound →
  AcceptingTableauCertificate machine input bound
boundedAcceptanceToAcceptingTableau machine input bound acceptance =
  let certificate =
        Run.boundedAcceptanceGivesFiniteCertificate
          machine input bound acceptance
  in acceptingTableauCertificate
      (Run.AcceptingRunCertificate.steps certificate)
      (Run.AcceptingRunCertificate.withinBound certificate)
      (Run.AcceptingRunCertificate.finalConfiguration certificate)
      (runCertificateToTableau
        (Run.AcceptingRunCertificate.run certificate))
      (Run.AcceptingRunCertificate.accepting certificate)

acceptingTableauToBoundedAcceptance :
  ∀ machine input bound →
  AcceptingTableauCertificate machine input bound →
  Machine.NondeterministicAcceptsWithin machine input bound
acceptingTableauToBoundedAcceptance machine input bound certificate =
  Run.finiteCertificateGivesBoundedAcceptance machine input bound
    (Run.acceptingRunCertificate
      (steps certificate)
      (withinBound certificate)
      (finish certificate)
      (tableauToRunCertificate (tableau certificate))
      (accepting certificate))

record BooleanCNFTableauBoundary
    (machine : Machine.NondeterministicMachine) : Set₁ where
  field
    Bit : Set
    ConfigurationEncoding : Set
    tableauCellVariables : Set
    exactlyOneSymbolPerCell : Set
    initialRowClauses : Set
    localWindowClauses : Set
    acceptingRowClauses : Set
    satisfyingAssignmentFromTableau : Set
    tableauFromSatisfyingAssignment : Set
    variableCountPolynomial : Set
    clauseCountPolynomial : Set
