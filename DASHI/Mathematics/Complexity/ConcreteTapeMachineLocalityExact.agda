module DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact where

------------------------------------------------------------------------
-- CONCRETE FINITE TAPE-MACHINE LOCALITY
--
-- A machine step is a literal contiguous radius-one rewrite:
--
--   common prefix ++ old 3-cell window ++ common suffix
--        ->
--   common prefix ++ new 3-cell window ++ common suffix.
--
-- RuleRealizesWindow has one constructor for each head direction, so the
-- six-cell transition pattern is no longer an opaque proposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

data Direction : Set where
  moveLeft : Direction
  stayPut : Direction
  moveRight : Direction

record FiniteEnumeration (A : Set) : Set₁ where
  field
    values : List A
    occurs : A → Set
    complete : (x : A) → occurs x

    decideEqual : A → A → Bool

    decideEqualRefl :
      (x : A) →
      decideEqual x x ≡ true

    decideEqualSound :
      ∀ {x y} →
      decideEqual x y ≡ true →
      x ≡ y

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

data RuleOccurs {State Symbol : Set} :
    TapeRule State Symbol →
    List (TapeRule State Symbol) →
    Set where
  ruleHere :
    ∀ {rule rest} →
    RuleOccurs rule (rule ∷ rest)

  ruleThere :
    ∀ {rule other rest} →
    RuleOccurs rule rest →
    RuleOccurs rule (other ∷ rest)

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

data RuleRealizesWindow
    (machine : ConcreteTapeMachine) :
    TapeRule (State machine) (Symbol machine) →
    SixCellWindow machine →
    Set where

  realizes-left :
    ∀ {q q' a b leftSymbol rightSymbol} →
    RuleRealizesWindow machine
      (tape-rule q a q' b moveLeft)
      (six-cell-window
        (plain leftSymbol)
        (headed q a)
        (plain rightSymbol)
        (headed q' leftSymbol)
        (plain b)
        (plain rightSymbol))

  realizes-stay :
    ∀ {q q' a b leftSymbol rightSymbol} →
    RuleRealizesWindow machine
      (tape-rule q a q' b stayPut)
      (six-cell-window
        (plain leftSymbol)
        (headed q a)
        (plain rightSymbol)
        (plain leftSymbol)
        (headed q' b)
        (plain rightSymbol))

  realizes-right :
    ∀ {q q' a b leftSymbol rightSymbol} →
    RuleRealizesWindow machine
      (tape-rule q a q' b moveRight)
      (six-cell-window
        (plain leftSymbol)
        (headed q a)
        (plain rightSymbol)
        (plain leftSymbol)
        (plain b)
        (headed q' rightSymbol))

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

record WindowRewriteOccurrence
    (machine : ConcreteTapeMachine)
    (before after : TapeRow machine)
    (window : SixCellWindow machine) : Set where
  field
    prefix suffix :
      List (TapeCell (State machine) (Symbol machine))

    beforeShape :
      cells before
      ≡ append prefix
          (oldLeft window ∷ oldCenter window ∷ oldRight window ∷ suffix)

    afterShape :
      cells after
      ≡ append prefix
          (newLeft window ∷ newCenter window ∷ newRight window ∷ suffix)

open WindowRewriteOccurrence public

record LocalStepWitness
    (machine : ConcreteTapeMachine)
    (before after : TapeRow machine) : Set₁ where
  field
    rule : TapeRule (State machine) (Symbol machine)
    ruleOccursInMachine :
      RuleOccurs rule (rules machine)
    window : SixCellWindow machine
    ruleIsConfigured : RuleRealizesWindow machine rule window
    occurrence : WindowRewriteOccurrence machine before after window

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
    transitionTableMembershipPaid : Bool
    exactDirectionalWindowRulesPaid : Bool
    contiguousRewriteOccurrencePaid : Bool
    localStepWitnessSemanticsPaid : Bool
    genericMachineAdapterPaid : Bool
    allOverlappingWindowsCharacterizationPaid : Bool
    runToCanonicalSATPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeMachineLocalityBoundary :
  ConcreteTapeMachineLocalityBoundary
canonicalConcreteTapeMachineLocalityBoundary =
  concrete-tape-machine-locality-boundary
    true true true true true false false false false
