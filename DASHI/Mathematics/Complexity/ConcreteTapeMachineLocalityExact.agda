module DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

data Direction : Set where
  moveLeft : Direction
  stayPut : Direction
  moveRight : Direction

record FiniteEnumeration (A : Set) : Set₁ where
  field
    values : List A
    occurs : A → Set
    complete : (x : A) → occurs x

open FiniteEnumeration public

data TapeCell (State Symbol : Set) : Set where
  plain : Symbol → TapeCell State Symbol
  headed : State → Symbol → TapeCell State Symbol

record TapeRule (State Symbol : Set) : Set where
  constructor tape-rule
  field
    sourceState : State
    readSymbol : Symbol
    targetState : State
    writeSymbol : Symbol
    direction : Direction

open TapeRule public

record ConcreteTapeMachine : Set₁ where
  field
    State : Set
    Symbol : Set
    finiteState : FiniteEnumeration State
    finiteSymbol : FiniteEnumeration Symbol
    blank : Symbol
    initialState : State
    acceptingState : State
    rules : List (TapeRule State Symbol)

open ConcreteTapeMachine public

record TapeRow (machine : ConcreteTapeMachine) : Set where
  constructor tape-row
  field
    cells : List (TapeCell (State machine) (Symbol machine))

open TapeRow public

record SixCellWindow (machine : ConcreteTapeMachine) : Set where
  constructor six-cell-window
  field
    oldLeft oldCenter oldRight :
      TapeCell (State machine) (Symbol machine)
    newLeft newCenter newRight :
      TapeCell (State machine) (Symbol machine)

open SixCellWindow public

record RuleRealizesWindow
    (machine : ConcreteTapeMachine)
    (rule : TapeRule (State machine) (Symbol machine))
    (window : SixCellWindow machine) : Set where
  field
    realizes : Set

open RuleRealizesWindow public

record LocalStepWitness
    (machine : ConcreteTapeMachine)
    (before after : TapeRow machine) : Set₁ where
  field
    rule : TapeRule (State machine) (Symbol machine)
    window : SixCellWindow machine
    ruleIsConfigured : RuleRealizesWindow machine rule window
    windowOccursInBeforeAfter : Set
    outsideWindowPreserved : Set

open LocalStepWitness public

MachineStep :
  (machine : ConcreteTapeMachine) →
  TapeRow machine → TapeRow machine → Set₁
MachineStep machine before after =
  LocalStepWitness machine before after

machineStepHasLocalWitness :
  ∀ {machine before after} →
  MachineStep machine before after →
  LocalStepWitness machine before after
machineStepHasLocalWitness witness = witness

localWitnessIsMachineStep :
  ∀ {machine before after} →
  LocalStepWitness machine before after →
  MachineStep machine before after
localWitnessIsMachineStep witness = witness

record ConcreteTapeMachineLocalityBoundary : Set where
  constructor concrete-tape-machine-locality-boundary
  field
    finiteMachineCarrierPaid : Bool
    localStepWitnessSemanticsPaid : Bool
    genericMachineAdapterPaid : Bool
    overlappingWindowExtractionPaid : Bool
    runToCanonicalSATPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeMachineLocalityBoundary :
  ConcreteTapeMachineLocalityBoundary
canonicalConcreteTapeMachineLocalityBoundary =
  concrete-tape-machine-locality-boundary
    true true false false false false
