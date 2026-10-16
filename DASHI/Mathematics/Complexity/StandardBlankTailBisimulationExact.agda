module DASHI.Mathematics.Complexity.StandardBlankTailBisimulationExact where

------------------------------------------------------------------------
-- IMPLICIT / EXPLICIT BLANK-TAIL BISIMULATION
--
-- Conventional split-tape semantics uses `[]` to denote an infinite blank tail.
-- Cook--Levin guarded rows materialise a finite number of those same blanks.
-- This owner quotients that representation choice without changing machine
-- control, scanned symbols, transitions or run length.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run

------------------------------------------------------------------------
-- 1. Semantic equality of finite list representatives of an infinite blank tail.
------------------------------------------------------------------------

listAtBlankDefault :
  ∀ {Symbol : Set} →
  Symbol → Nat → List Symbol → Symbol
listAtBlankDefault blank zero [] = blank
listAtBlankDefault blank zero (x ∷ xs) = x
listAtBlankDefault blank (suc n) [] = blank
listAtBlankDefault blank (suc n) (x ∷ xs) =
  listAtBlankDefault blank n xs

ListBlankTailEq :
  ∀ {Symbol : Set} →
  Symbol → List Symbol → List Symbol → Set
ListBlankTailEq blank left right =
  (n : Nat) →
  listAtBlankDefault blank n left
  ≡ listAtBlankDefault blank n right

listBlankTailEqRefl :
  ∀ {Symbol : Set}
    (blank : Symbol)
    (xs : List Symbol) →
  ListBlankTailEq blank xs xs
listBlankTailEqRefl blank xs n = refl

listBlankTailEqSym :
  ∀ {Symbol : Set} {blank : Symbol} {xs ys : List Symbol} →
  ListBlankTailEq blank xs ys →
  ListBlankTailEq blank ys xs
listBlankTailEqSym eq n = sym (eq n)

consPreservesBlankTailEq :
  ∀ {Symbol : Set} {blank x : Symbol} {xs ys : List Symbol} →
  ListBlankTailEq blank xs ys →
  ListBlankTailEq blank (x ∷ xs) (x ∷ ys)
consPreservesBlankTailEq eq zero = refl
consPreservesBlankTailEq eq (suc n) = eq n

headsEqualFromBlankTailEq :
  ∀ {Symbol : Set} {blank x y : Symbol} {xs ys : List Symbol} →
  ListBlankTailEq blank (x ∷ xs) (y ∷ ys) →
  x ≡ y
headsEqualFromBlankTailEq eq = eq zero

tailsEqualFromBlankTailEq :
  ∀ {Symbol : Set} {blank x y : Symbol} {xs ys : List Symbol} →
  ListBlankTailEq blank (x ∷ xs) (y ∷ ys) →
  ListBlankTailEq blank xs ys
tailsEqualFromBlankTailEq eq n = eq (suc n)

emptyHeadEqual :
  ∀ {Symbol : Set} {blank y : Symbol} {ys : List Symbol} →
  ListBlankTailEq blank [] (y ∷ ys) →
  blank ≡ y
emptyHeadEqual eq = eq zero

emptyTailEqual :
  ∀ {Symbol : Set} {blank y : Symbol} {ys : List Symbol} →
  ListBlankTailEq blank [] (y ∷ ys) →
  ListBlankTailEq blank [] ys
emptyTailEqual eq n = eq (suc n)

headEmptyEqual :
  ∀ {Symbol : Set} {blank x : Symbol} {xs : List Symbol} →
  ListBlankTailEq blank (x ∷ xs) [] →
  x ≡ blank
headEmptyEqual eq = eq zero

tailEmptyEqual :
  ∀ {Symbol : Set} {blank x : Symbol} {xs : List Symbol} →
  ListBlankTailEq blank (x ∷ xs) [] →
  ListBlankTailEq blank xs []
tailEmptyEqual eq n = eq (suc n)

------------------------------------------------------------------------
-- 2. Configuration equivalence modulo explicit far-tail blanks.
------------------------------------------------------------------------

record ConfigurationBlankTailEq
    {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    (left right : Standard.StandardConfiguration machine) : Set where
  field
    stateEq : Standard.state left ≡ Standard.state right
    scannedEq : Standard.scanned left ≡ Standard.scanned right
    leftEq :
      ListBlankTailEq
        (Standard.blank machine)
        (Standard.left left)
        (Standard.left right)
    rightEq :
      ListBlankTailEq
        (Standard.blank machine)
        (Standard.right left)
        (Standard.right right)

open ConfigurationBlankTailEq public

configurationBlankTailEqRefl :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    (configuration : Standard.StandardConfiguration machine) →
  ConfigurationBlankTailEq configuration configuration
configurationBlankTailEqRefl {machine = machine} configuration = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = listBlankTailEqRefl (Standard.blank machine) (Standard.left configuration)
  ; rightEq = listBlankTailEqRefl (Standard.blank machine) (Standard.right configuration)
  }

------------------------------------------------------------------------
-- 3. A selected transition preserves blank-tail equivalence.
------------------------------------------------------------------------

standardApplyTransitionPreservesBlankTailEq :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    {left right : Standard.StandardConfiguration machine} →
  ConfigurationBlankTailEq left right →
  (selected : Standard.StandardTransition State Symbol) →
  ConfigurationBlankTailEq
    (Standard.standardApplyTransition machine left selected)
    (Standard.standardApplyTransition machine right selected)
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration leftTape leftState leftScanned leftRight}
    {right = Standard.standard-configuration rightTape rightState rightScanned rightRight}
    eq
    (Standard.standard-transition target write Local.stayPut) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = leftEq eq
  ; rightEq = rightEq eq
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration [] leftState leftScanned leftRight}
    {right = Standard.standard-configuration [] rightState rightScanned rightRight}
    eq
    (Standard.standard-transition target write Local.moveLeft) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = listBlankTailEqRefl (Standard.blank machine) []
  ; rightEq = consPreservesBlankTailEq (rightEq eq)
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration [] leftState leftScanned leftRight}
    {right = Standard.standard-configuration (r ∷ rs) rightState rightScanned rightRight}
    eq
    (Standard.standard-transition target write Local.moveLeft)
    rewrite sym (emptyHeadEqual (leftEq eq)) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = emptyTailEqual (leftEq eq)
  ; rightEq = consPreservesBlankTailEq (rightEq eq)
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration (l ∷ ls) leftState leftScanned leftRight}
    {right = Standard.standard-configuration [] rightState rightScanned rightRight}
    eq
    (Standard.standard-transition target write Local.moveLeft)
    rewrite headEmptyEqual (leftEq eq) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = tailEmptyEqual (leftEq eq)
  ; rightEq = consPreservesBlankTailEq (rightEq eq)
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration (l ∷ ls) leftState leftScanned leftRight}
    {right = Standard.standard-configuration (r ∷ rs) rightState rightScanned rightRight}
    eq
    (Standard.standard-transition target write Local.moveLeft)
    rewrite headsEqualFromBlankTailEq (leftEq eq) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = tailsEqualFromBlankTailEq (leftEq eq)
  ; rightEq = consPreservesBlankTailEq (rightEq eq)
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration leftTape leftState leftScanned []}
    {right = Standard.standard-configuration rightTape rightState rightScanned []}
    eq
    (Standard.standard-transition target write Local.moveRight) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = consPreservesBlankTailEq (leftEq eq)
  ; rightEq = listBlankTailEqRefl (Standard.blank machine) []
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration leftTape leftState leftScanned []}
    {right = Standard.standard-configuration rightTape rightState rightScanned (r ∷ rs)}
    eq
    (Standard.standard-transition target write Local.moveRight)
    rewrite sym (emptyHeadEqual (rightEq eq)) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = consPreservesBlankTailEq (leftEq eq)
  ; rightEq = emptyTailEqual (rightEq eq)
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration leftTape leftState leftScanned (l ∷ ls)}
    {right = Standard.standard-configuration rightTape rightState rightScanned []}
    eq
    (Standard.standard-transition target write Local.moveRight)
    rewrite headEmptyEqual (rightEq eq) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = consPreservesBlankTailEq (leftEq eq)
  ; rightEq = tailEmptyEqual (rightEq eq)
  }
standardApplyTransitionPreservesBlankTailEq machine
    {left = Standard.standard-configuration leftTape leftState leftScanned (l ∷ ls)}
    {right = Standard.standard-configuration rightTape rightState rightScanned (r ∷ rs)}
    eq
    (Standard.standard-transition target write Local.moveRight)
    rewrite headsEqualFromBlankTailEq (rightEq eq) = record
  { stateEq = refl
  ; scannedEq = refl
  ; leftEq = consPreservesBlankTailEq (leftEq eq)
  ; rightEq = tailsEqualFromBlankTailEq (rightEq eq)
  }

------------------------------------------------------------------------
-- 4. `standardNext` is a bisimulation on the quotient.
------------------------------------------------------------------------

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

standardNextPreservesBlankTailEq :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    {left right nextLeft : Standard.StandardConfiguration machine} →
  ConfigurationBlankTailEq left right →
  Standard.standardNext machine left ≡ just nextLeft →
  Σ (Standard.StandardConfiguration machine) λ nextRight →
    (Standard.standardNext machine right ≡ just nextRight)
    × ConfigurationBlankTailEq nextLeft nextRight
standardNextPreservesBlankTailEq machine
    {left = left} {right = right} {nextLeft = nextLeft}
    eq edge
  with stateEq eq | scannedEq eq
... | refl | refl
  with Standard.transition machine (Standard.state left) (Standard.scanned left)
... | nothing with edge
... | ()
... | just selected
  with justInjective edge
... | refl =
  Standard.standardApplyTransition machine right selected
  , refl
  , standardApplyTransitionPreservesBlankTailEq machine eq selected

------------------------------------------------------------------------
-- 5. Exact-run transport preserves the literal number of steps.
------------------------------------------------------------------------

transportExactRunAcrossBlankTailEq :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {steps : Nat}
    {leftStart rightStart leftFinish : Standard.StandardConfiguration machine} →
  ConfigurationBlankTailEq leftStart rightStart →
  Run.StandardExactRun machine steps leftStart leftFinish →
  Σ (Standard.StandardConfiguration machine) λ rightFinish →
    Run.StandardExactRun machine steps rightStart rightFinish
    × ConfigurationBlankTailEq leftFinish rightFinish
transportExactRunAcrossBlankTailEq startEq Run.standardRunDone =
  _ , Run.standardRunDone , startEq
transportExactRunAcrossBlankTailEq startEq
    (Run.standardRunStep edge rest)
  with standardNextPreservesBlankTailEq _ startEq edge
... | nextRight , rightEdge , nextEq
  with transportExactRunAcrossBlankTailEq nextEq rest
... | finishRight , rightRest , finishEq =
  finishRight
  , Run.standardRunStep rightEdge rightRest
  , finishEq

------------------------------------------------------------------------
-- 6. Source-level boundary receipt.
------------------------------------------------------------------------

record BlankTailBisimulationBoundary : Set where
  constructor blank-tail-bisimulation-boundary
  field
    implicitAndExplicitBlankTailsIdentified : Bool
    selectedTransitionPreservesEquivalence : Bool
    standardNextPreservesEquivalence : Bool
    exactRunLengthPreserved : Bool
    machineStatePreserved : Bool
    cookPaddingChoosesRuntime : Bool

blankTailBisimulationBoundary : BlankTailBisimulationBoundary
blankTailBisimulationBoundary =
  blank-tail-bisimulation-boundary
    true true true true true false

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- A finite explicit blank margin is now a representation refinement of the
-- ordinary split-tape semantics with implicit blank tails.  Transport preserves
-- the exact number of machine steps and control state.  The remaining guarded
-- receipt payment is therefore only the concrete theorem that the canonical
-- input and `guardedStandardStart(input,T)` are related by this equivalence.
------------------------------------------------------------------------
