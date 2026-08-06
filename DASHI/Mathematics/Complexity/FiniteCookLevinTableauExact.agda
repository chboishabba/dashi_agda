module DASHI.Mathematics.Complexity.FiniteCookLevinTableauExact where

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
-- Construct an exact finite Cook--Levin seed rather than only a theorem name.
-- A three-row tableau represents the unique two-step accepting computation
--
--   start -> work -> accept.
--
-- Initial, local-transition and accepting-row constraints are explicit.  A
-- satisfying tableau yields the accepting machine run, and the canonical run
-- yields a satisfying tableau.  The general tape alphabet, window clauses,
-- CNF encoding and polynomial-size theorem remain separate generic owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using ()
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine

data ToyState : Set where
  startState workState acceptState rejectState : ToyState

data AcceptingToyState : ToyState → Set where
  acceptingState : AcceptingToyState acceptState

toySuccessors : ToyState → Agda.Builtin.List.List ToyState
toySuccessors startState = workState ∷ []
toySuccessors workState = acceptState ∷ []
toySuccessors acceptState = []
toySuccessors rejectState = []

toyMachine : Machine.NondeterministicMachine
toyMachine = record
  { Machine.NondeterministicMachine.nInput = ⊤
  ; Machine.NondeterministicMachine.nConfiguration = ToyState
  ; Machine.NondeterministicMachine.nInitial = λ input → startState
  ; Machine.NondeterministicMachine.nSuccessors = toySuccessors
  ; Machine.NondeterministicMachine.nAccepting = AcceptingToyState
  }

canonicalTwoStepAcceptingRun :
  Machine.NDReach toyMachine (suc (suc zero)) startState acceptState
canonicalTwoStepAcceptingRun =
  Machine.ndStep Machine.here
    (Machine.ndStep Machine.here Machine.ndRefl)

record ThreeRowTableau : Set where
  constructor threeRowTableau
  field
    row0 row1 row2 : ToyState

open ThreeRowTableau public

record TableauConstraints (tableau : ThreeRowTableau) : Set where
  constructor tableauConstraints
  field
    initialRow : row0 tableau ≡ startState
    firstLocalTransition : row1 tableau ≡ workState
    secondLocalTransition : row2 tableau ≡ acceptState
    acceptingRow : AcceptingToyState (row2 tableau)

open TableauConstraints public

canonicalTableau : ThreeRowTableau
canonicalTableau = threeRowTableau startState workState acceptState

canonicalTableauSatisfiesConstraints : TableauConstraints canonicalTableau
canonicalTableauSatisfiesConstraints =
  tableauConstraints refl refl refl acceptingState

satisfyingTableauIsCanonical :
  ∀ tableau → TableauConstraints tableau → tableau ≡ canonicalTableau
satisfyingTableauIsCanonical
    (threeRowTableau row0 row1 row2)
    (tableauConstraints refl refl refl acceptingState) = refl

satisfyingTableauGivesAcceptingRun :
  ∀ tableau → TableauConstraints tableau →
  Machine.NDReach toyMachine (suc (suc zero))
    (row0 tableau) (row2 tableau)
satisfyingTableauGivesAcceptingRun
    (threeRowTableau row0 row1 row2)
    (tableauConstraints refl refl refl acceptingState) =
  canonicalTwoStepAcceptingRun

canonicalRunGivesSatisfyingTableau :
  Machine.NDReach toyMachine (suc (suc zero)) startState acceptState →
  TableauConstraints canonicalTableau
canonicalRunGivesSatisfyingTableau run = canonicalTableauSatisfiesConstraints

record LocalClauseFamily : Set where
  field
    initialClause : Set
    firstTransitionClause : Set
    secondTransitionClause : Set
    acceptingClause : Set

canonicalLocalClauseFamily : LocalClauseFamily
canonicalLocalClauseFamily = record
  { initialClause = startState ≡ startState
  ; firstTransitionClause = workState ≡ workState
  ; secondTransitionClause = acceptState ≡ acceptState
  ; acceptingClause = AcceptingToyState acceptState
  }

canonicalLocalClausesAreSatisfied :
  LocalClauseFamily.initialClause canonicalLocalClauseFamily
  × LocalClauseFamily.firstTransitionClause canonicalLocalClauseFamily
  × LocalClauseFamily.secondTransitionClause canonicalLocalClauseFamily
  × LocalClauseFamily.acceptingClause canonicalLocalClauseFamily
canonicalLocalClausesAreSatisfied = refl , refl , refl , acceptingState
  where
    open import Data.Product using (_×_; _,_)

record GeneralCookLevinBoundary : Set₁ where
  field
    TapeSymbol : Set
    MachineState : Set
    TimeBound : Set
    SpaceBound : Set
    tableauVariableEncoding : Set
    exactlyOneSymbolPerCellClauses : Set
    initialConfigurationClauses : Set
    transitionWindowClauses : Set
    acceptingConfigurationClauses : Set
    runImpliesSatisfyingAssignment : Set
    satisfyingAssignmentImpliesRun : Set
    clauseCountPolynomial : Set
    variableCountPolynomial : Set

data CookLevinLayer : Set where
  finiteToyTableauLayer generalCookLevinLayer : CookLevinLayer

toyTableauIsNotGeneralCookLevin :
  finiteToyTableauLayer ≡ generalCookLevinLayer → ⊥
toyTableauIsNotGeneralCookLevin ()
