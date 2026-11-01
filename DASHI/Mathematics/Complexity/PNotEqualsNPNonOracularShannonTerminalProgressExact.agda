module DASHI.Mathematics.Complexity.PNotEqualsNPNonOracularShannonTerminalProgressExact where

------------------------------------------------------------------------
-- NON-ORACULAR SHANNON TERMINALITY / PROGRESS
--
-- The existing Q1 constructors are Maybe-valued:
--
--   state -> Maybe run
--
-- so a constructor may return nothing at an arbitrary positive-arity state.
-- That makes residual-width lower bounds avoidable unless terminality itself is
-- constrained.
--
-- This owner adds the smallest structural rule compatible with the literal
-- Shannon carrier:
--
--   variableBound(currentFormula) = 0      -> stop
--   variableBound(currentFormula) = suc n  -> return an arity-admitted run
--
-- Zero arity is non-oracular: there is no remaining Shannon choice, and the
-- existing arity/terminal admission evaluates zero-variable descendants
-- structurally.  No SAT oracle is added here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as FutureSAT
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width

------------------------------------------------------------------------
-- Structural arity of one Q2 state.
------------------------------------------------------------------------

stateVariableBound :
  Q2.BoundedSelfReferenceState →
  Nat
stateVariableBound state =
  Bridge.formulaVariableBound
    (Q2.currentFormula state)

------------------------------------------------------------------------
-- The Q2 state's indexed root is the literal Shannon root already used by the
-- future-observation machinery.
------------------------------------------------------------------------

stateRestrictionRoot :
  (state : Q2.BoundedSelfReferenceState) →
  Family.RestrictionNode
    (Bridge.cookToIndexed
      (Q2.currentFormula state))
stateRestrictionRoot state =
  Family.rootNode
    (Bridge.cookToIndexed
      (Q2.currentFormula state))

------------------------------------------------------------------------
-- Positive variable bound is not an arbitrary live-state declaration.  It is
-- exactly enough evidence for one Shannon action to be admissible at the root.
------------------------------------------------------------------------

positiveStateIsShannonNonTerminal :
  (state : Q2.BoundedSelfReferenceState) →
  (remaining : Nat) →
  stateVariableBound state ≡ suc remaining →
  FutureSAT.NonTerminal
    (stateRestrictionRoot state)
positiveStateIsShannonNonTerminal state remaining positive =
  remaining , positive

------------------------------------------------------------------------
-- Conversely, zero variable bound already has the existing non-oracular
-- terminal observation: literal evaluation under the unique empty assignment.
------------------------------------------------------------------------

zeroStateHasStructuralTerminalObservation :
  (state : Q2.BoundedSelfReferenceState) →
  stateVariableBound state ≡ zero →
  Σ Bool
    (λ value →
      FutureSAT.restrictionObservation
        (stateRestrictionRoot state)
      ≡
      FutureSAT.terminal value)
zeroStateHasStructuralTerminalObservation state zeroBound
    rewrite zeroBound =
  SAT.evaluate
    (Bridge.cookToIndexed
      (Q2.currentFormula state))
    FutureSAT.emptyAssignment
  ,
  refl

------------------------------------------------------------------------
-- Constructor with exact structural terminal policy.
------------------------------------------------------------------------

record NonOracularShannonTerminalConstructor : Set₁ where
  constructor non-oracular-shannon-terminal-constructor
  field
    constructor :
      ArityTerminal.ArityTerminalAdmittedStateConstructor

    zeroArityStops :
      (state : Q2.BoundedSelfReferenceState) →
      stateVariableBound state ≡ zero →
      constructor state ≡ nothing

    positiveArityContinues :
      (state : Q2.BoundedSelfReferenceState) →
      (remaining : Nat) →
      stateVariableBound state ≡ suc remaining →
      Σ
        (ArityTerminal.ArityTerminalAdmittedConstructionRun state)
        (λ run →
          constructor state ≡ just run)

open NonOracularShannonTerminalConstructor public

------------------------------------------------------------------------
-- The old always-stop escape hatch is excluded at every positive-arity state.
------------------------------------------------------------------------
-- Cleaner exclusion theorem stated directly at the arity-terminal constructor
-- surface: a constructor that is definitionally always nothing cannot satisfy
-- positiveArityContinues.
------------------------------------------------------------------------

alwaysNothingArityConstructor :
  ArityTerminal.ArityTerminalAdmittedStateConstructor
alwaysNothingArityConstructor state =
  nothing

alwaysNothingCannotContinue :
  (state : Q2.BoundedSelfReferenceState) →
  (remaining : Nat) →
  stateVariableBound state ≡ suc remaining →
  Σ
    (ArityTerminal.ArityTerminalAdmittedConstructionRun state)
    (λ run →
      alwaysNothingArityConstructor state ≡ just run)
  →
  ⊥
alwaysNothingCannotContinue state remaining positive (run , ())

------------------------------------------------------------------------
-- Concrete separation witness:
--
-- the Shannon action system says this one-variable root is nonterminal, while
-- the old Maybe-valued constructor surface still permits immediate stopping.
------------------------------------------------------------------------

oneVariableState :
  Q2.BoundedSelfReferenceState
oneVariableState =
  Q2.bounded-self-reference-state
    (Cook.variable zero)
    zero
    zero
    (suc zero)
    stateFits
  where
    stateFits :
      Size.formulaNodeCount (Cook.variable zero)
        + (zero + zero)
      ≤
      suc zero
    stateFits =
      NatP.≤-refl

oneVariableStateHasPositiveBound :
  stateVariableBound oneVariableState
  ≡
  suc zero
oneVariableStateHasPositiveBound =
  refl

oneVariableStateIsShannonNonTerminal :
  FutureSAT.NonTerminal
    (stateRestrictionRoot oneVariableState)
oneVariableStateIsShannonNonTerminal =
  positiveStateIsShannonNonTerminal
    oneVariableState
    zero
    oneVariableStateHasPositiveBound

alwaysNothingStopsAtShannonNonTerminal :
  alwaysNothingArityConstructor
    oneVariableState
  ≡
  nothing
alwaysNothingStopsAtShannonNonTerminal =
  refl

------------------------------------------------------------------------
-- Thus Shannon nonterminality and Q2 progress are presently distinct notions.
-- The missing semantic entitlement is a bridge between them.
------------------------------------------------------------------------

record ShannonProgressSeparation : Set₁ where
  constructor shannon-progress-separation
  field
    state :
      Q2.BoundedSelfReferenceState

    shannonNonTerminal :
      FutureSAT.NonTerminal
        (stateRestrictionRoot state)

    constructorStops :
      alwaysNothingArityConstructor state
      ≡
      nothing

open ShannonProgressSeparation public

concreteShannonProgressSeparation :
  ShannonProgressSeparation
concreteShannonProgressSeparation =
  shannon-progress-separation
    oneVariableState
    oneVariableStateIsShannonNonTerminal
    alwaysNothingStopsAtShannonNonTerminal

------------------------------------------------------------------------
-- Compile the structurally disciplined constructor to the already-existing Q2
-- step system.  No new execution semantics are introduced.
------------------------------------------------------------------------

nonOracularConstructorToQ2StepSystem :
  NonOracularShannonTerminalConstructor →
  Q2.BoundedSelfReferenceStepSystem
nonOracularConstructorToQ2StepSystem system =
  ArityTerminal.arityTerminalConstructorToQ2StepSystem
    (constructor system)

------------------------------------------------------------------------
-- Positive arity now places residual width on the live construction path.
------------------------------------------------------------------------

positiveArityProgressForcesTripleWidth :
  ∀ {next total : Nat}
    (system : NonOracularShannonTerminalConstructor)
    (state : Q2.BoundedSelfReferenceState)
    (remaining : Nat) →
  stateVariableBound state ≡ suc remaining →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  Width.triple total
  <
  Q2.recursiveMeasure state
positiveArityProgressForcesTripleWidth
    system
    state
    remaining
    positive
    stack
    with positiveArityContinues
           system
           state
           remaining
           positive
... | run , returnsRun =
  Width.tripleLayeredResidualWidthStrictlyBelowCurrentMeasure
    run
    stack

------------------------------------------------------------------------
-- A one-layer version is enough for an exponential donor: successful positive
-- progress must have at least as many states as any witnessed residual layer.
------------------------------------------------------------------------

positiveArityRunExists :
  (system : NonOracularShannonTerminalConstructor) →
  (state : Q2.BoundedSelfReferenceState) →
  (remaining : Nat) →
  stateVariableBound state ≡ suc remaining →
  Σ
    (ArityTerminal.ArityTerminalAdmittedConstructionRun state)
    (λ run →
      constructor system state ≡ just run)
positiveArityRunExists =
  positiveArityContinues

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The width route now has an exact structural coverage seam:
--
--   positive Shannon arity
--      -> successful arity-admitted construction
--      -> residual-width state-count lower bound
--      -> charged graph-budget lower bound.
--
-- What is NOT proved here is that the current Q2/self-diagonal semantics are
-- entitled to this terminal policy.  Establishing that entitlement, or finding
-- a weaker independently justified live-state criterion, remains the next
-- semantic question.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- ARBITRARY-FORMULA STATE EMBEDDING
--
-- BoundedSelfReferenceState presently imposes no provenance predicate on the
-- current Cook formula.  Therefore every ordinary formula can be embedded as a
-- Q2 state with zero persistent program/rebinding overhead and a budget exactly
-- equal to its represented recursive measure.
------------------------------------------------------------------------

arbitraryFormulaState :
  Cook.BooleanFormula →
  Q2.BoundedSelfReferenceState
arbitraryFormulaState formula =
  Q2.bounded-self-reference-state
    formula
    zero
    zero
    (Size.formulaNodeCount formula + (zero + zero))
    NatP.≤-refl

arbitraryFormulaStateFormulaExact :
  (formula : Cook.BooleanFormula) →
  Q2.currentFormula
    (arbitraryFormulaState formula)
  ≡ formula
arbitraryFormulaStateFormulaExact formula =
  refl

arbitraryFormulaStateMeasureExact :
  (formula : Cook.BooleanFormula) →
  Q2.recursiveMeasure
    (arbitraryFormulaState formula)
  ≡
  Size.formulaNodeCount formula + (zero + zero)
arbitraryFormulaStateMeasureExact formula =
  refl

------------------------------------------------------------------------
-- Generic high-width obstruction to GLOBAL positive-arity progress.
--
-- If one arbitrary formula already has a witnessed layered width whose three
-- transition-graph cells per state meet or exceed the Q2 recursive measure,
-- then no NonOracularShannonTerminalConstructor can satisfy its present
-- all-positive-arity continuation policy.
------------------------------------------------------------------------

globalPositiveProgressBlockedByHighWidthFormula :
  ∀ {next total remaining : Nat}
    (system : NonOracularShannonTerminalConstructor)
    (formula : Cook.BooleanFormula) →
  Bridge.formulaVariableBound formula
    ≡ suc remaining →
  Width.ResidualWidthStack
    {root = Bridge.cookToIndexed formula}
    next
    total →
  Q2.recursiveMeasure
      (arbitraryFormulaState formula)
    ≤
    Width.triple total →
  ⊥
globalPositiveProgressBlockedByHighWidthFormula
    {total = total}
    {remaining = remaining}
    system
    formula
    positive
    stack
    measureBelowWidth =
  NatP.<⇒≱
    forcedWidthBelowMeasure
    measureBelowWidth
  where
    forcedWidthBelowMeasure :
      Width.triple total
      <
      Q2.recursiveMeasure
        (arbitraryFormulaState formula)
    forcedWidthBelowMeasure =
      positiveArityProgressForcesTripleWidth
        system
        (arbitraryFormulaState formula)
        remaining
        positive
        stack

------------------------------------------------------------------------
-- FRONTIER CORRECTION
--
-- Consequently the current global terminal policy is too strong unless the
-- live Q2 carrier is first narrowed by a proved self-instantiation provenance
-- law (or unless one proves the required width budget for every arbitrary
-- positive-arity Cook formula, which is exactly what the generic width donors
-- are designed to falsify).
--
-- The next positive theorem must therefore be scoped to an independently
-- characterized image/reachable subset of the ACTUAL bounded diagonal body.
-- Merely saying "positive Shannon arity means continue" over the present Q2
-- carrier silently quantifies over all Cook formulas.
------------------------------------------------------------------------
