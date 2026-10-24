module DASHI.Mathematics.Complexity.StandardBlankTailEquivalenceExact where

------------------------------------------------------------------------
-- STANDARD SPLIT-TAPE EQUIVALENCE MODULO FINITE FAR-TAIL BLANKS
--
-- A finite split-tape list represents an infinite blank tail.  Therefore
-- appending finitely many blank symbols at the FAR end of either side must not
-- change the represented machine execution.  This owner makes that operational:
--
--   * list equivalence permits only extra trailing blanks;
--   * one ordinary standard step preserves configuration equivalence;
--   * every exact run transports edge-for-edge with identical step count.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run

------------------------------------------------------------------------
-- All-blank tails and equality modulo a finite blank suffix.
------------------------------------------------------------------------

data AllBlank {Symbol : Set} (blank : Symbol) : List Symbol → Set where
  allBlankNil : AllBlank blank []
  allBlankCons : ∀ {rest} → AllBlank blank rest →
    AllBlank blank (blank ∷ rest)

data BlankTailEq {Symbol : Set} (blank : Symbol) :
    List Symbol → List Symbol → Set where
  bothNil : BlankTailEq blank [] []
  leftEmpty : ∀ {right} → AllBlank blank right →
    BlankTailEq blank [] right
  rightEmpty : ∀ {left} → AllBlank blank left →
    BlankTailEq blank left []
  bothCons : ∀ {symbol left right} →
    BlankTailEq blank left right →
    BlankTailEq blank (symbol ∷ left) (symbol ∷ right)

blankTailRefl :
  ∀ {Symbol : Set} {blank : Symbol} (xs : List Symbol) →
  BlankTailEq blank xs xs
blankTailRefl [] = bothNil
blankTailRefl (x ∷ xs) = bothCons (blankTailRefl xs)

allBlankTailLeft :
  ∀ {Symbol : Set} {blank : Symbol} {xs : List Symbol} →
  AllBlank blank xs → BlankTailEq blank [] xs
allBlankTailLeft = leftEmpty

allBlankTailRight :
  ∀ {Symbol : Set} {blank : Symbol} {xs : List Symbol} →
  AllBlank blank xs → BlankTailEq blank xs []
allBlankTailRight = rightEmpty

blankTailSym :
  ∀ {Symbol : Set} {blank : Symbol} {left right : List Symbol} →
  BlankTailEq blank left right → BlankTailEq blank right left
blankTailSym bothNil = bothNil
blankTailSym (leftEmpty all) = rightEmpty all
blankTailSym (rightEmpty all) = leftEmpty all
blankTailSym (bothCons rest) = bothCons (blankTailSym rest)

------------------------------------------------------------------------
-- Same control/scanned symbol, side lists equal modulo far blanks.
------------------------------------------------------------------------

data ConfigurationBlankTailEq
    {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol) :
    Standard.StandardConfiguration machine →
    Standard.StandardConfiguration machine → Set where
  configurationEq :
    ∀ {leftA leftB q a rightA rightB} →
    BlankTailEq (Standard.blank machine) leftA leftB →
    BlankTailEq (Standard.blank machine) rightA rightB →
    ConfigurationBlankTailEq machine
      (Standard.standard-configuration leftA q a rightA)
      (Standard.standard-configuration leftB q a rightB)

configurationBlankTailRefl :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    (configuration : Standard.StandardConfiguration machine) →
  ConfigurationBlankTailEq machine configuration configuration
configurationBlankTailRefl
    (Standard.standard-configuration left q a right) =
  configurationEq (blankTailRefl left) (blankTailRefl right)

------------------------------------------------------------------------
-- Same selected transition preserves blank-tail equivalence.
------------------------------------------------------------------------

applyMoveLeftRelated :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {leftA leftB rightA rightB q a q' b}
    (leftRel : BlankTailEq (Standard.blank machine) leftA leftB)
    (rightRel : BlankTailEq (Standard.blank machine) rightA rightB) →
  ConfigurationBlankTailEq machine
    (Standard.standardApplyTransition machine
      (Standard.standard-configuration leftA q a rightA)
      (Standard.standard-transition q' b Local.moveLeft))
    (Standard.standardApplyTransition machine
      (Standard.standard-configuration leftB q a rightB)
      (Standard.standard-transition q' b Local.moveLeft))
applyMoveLeftRelated bothNil rightRel =
  configurationEq bothNil (bothCons rightRel)
applyMoveLeftRelated (leftEmpty allBlankNil) rightRel =
  configurationEq bothNil (bothCons rightRel)
applyMoveLeftRelated
    (leftEmpty (allBlankCons restBlank)) rightRel =
  configurationEq (leftEmpty restBlank) (bothCons rightRel)
applyMoveLeftRelated (rightEmpty allBlankNil) rightRel =
  configurationEq bothNil (bothCons rightRel)
applyMoveLeftRelated
    (rightEmpty (allBlankCons restBlank)) rightRel =
  configurationEq (rightEmpty restBlank) (bothCons rightRel)
applyMoveLeftRelated (bothCons leftRel) rightRel =
  configurationEq leftRel (bothCons rightRel)

applyMoveRightRelated :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {leftA leftB rightA rightB q a q' b}
    (leftRel : BlankTailEq (Standard.blank machine) leftA leftB)
    (rightRel : BlankTailEq (Standard.blank machine) rightA rightB) →
  ConfigurationBlankTailEq machine
    (Standard.standardApplyTransition machine
      (Standard.standard-configuration leftA q a rightA)
      (Standard.standard-transition q' b Local.moveRight))
    (Standard.standardApplyTransition machine
      (Standard.standard-configuration leftB q a rightB)
      (Standard.standard-transition q' b Local.moveRight))
applyMoveRightRelated leftRel bothNil =
  configurationEq (bothCons leftRel) bothNil
applyMoveRightRelated leftRel (leftEmpty allBlankNil) =
  configurationEq (bothCons leftRel) bothNil
applyMoveRightRelated leftRel
    (leftEmpty (allBlankCons restBlank)) =
  configurationEq (bothCons leftRel) (leftEmpty restBlank)
applyMoveRightRelated leftRel (rightEmpty allBlankNil) =
  configurationEq (bothCons leftRel) bothNil
applyMoveRightRelated leftRel
    (rightEmpty (allBlankCons restBlank)) =
  configurationEq (bothCons leftRel) (rightEmpty restBlank)
applyMoveRightRelated leftRel (bothCons rightRel) =
  configurationEq (bothCons leftRel) rightRel

applyTransitionRelated :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {beforeA beforeB : Standard.StandardConfiguration machine}
    (related : ConfigurationBlankTailEq machine beforeA beforeB)
    (selected : Standard.StandardTransition State Symbol) →
  ConfigurationBlankTailEq machine
    (Standard.standardApplyTransition machine beforeA selected)
    (Standard.standardApplyTransition machine beforeB selected)
applyTransitionRelated
    (configurationEq leftRel rightRel)
    (Standard.standard-transition q' b Local.moveLeft) =
  applyMoveLeftRelated leftRel rightRel
applyTransitionRelated
    (configurationEq leftRel rightRel)
    (Standard.standard-transition q' b Local.moveRight) =
  applyMoveRightRelated leftRel rightRel
applyTransitionRelated
    (configurationEq leftRel rightRel)
    (Standard.standard-transition q' b Local.stayPut) =
  configurationEq leftRel rightRel

------------------------------------------------------------------------
-- One-step bisimulation.
------------------------------------------------------------------------

record TransportedStep
    {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {beforeA afterA beforeB : Standard.StandardConfiguration machine}
    (related : ConfigurationBlankTailEq machine beforeA beforeB) : Set where
  field
    afterB : Standard.StandardConfiguration machine
    targetEdge : Standard.standardNext machine beforeB ≡ just afterB
    afterRelated : ConfigurationBlankTailEq machine afterA afterB

open TransportedStep public

transportOneStep :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {beforeA afterA beforeB : Standard.StandardConfiguration machine}
    (related : ConfigurationBlankTailEq machine beforeA beforeB) →
  Standard.standardNext machine beforeA ≡ just afterA →
  TransportedStep related
transportOneStep
    {machine = machine}
    {beforeA = Standard.standard-configuration leftA q a rightA}
    {beforeB = Standard.standard-configuration leftB .q .a rightB}
    (configurationEq leftRel rightRel)
    sourceEdge
  with Standard.transition machine q a
... | nothing
  with sourceEdge
... | ()
... | just selected
  with sourceEdge
... | refl = record
  { afterB =
      Standard.standardApplyTransition machine
        (Standard.standard-configuration leftB q a rightB) selected
  ; targetEdge = refl
  ; afterRelated =
      applyTransitionRelated
        (configurationEq leftRel rightRel) selected
  }

------------------------------------------------------------------------
-- Exact run transport, preserving step count.
------------------------------------------------------------------------

record TransportedRun
    {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {steps : Nat}
    {startA finishA startB : Standard.StandardConfiguration machine}
    (startRelated : ConfigurationBlankTailEq machine startA startB)
    (source : Run.StandardExactRun machine steps startA finishA) : Set where
  field
    finishB : Standard.StandardConfiguration machine
    target : Run.StandardExactRun machine steps startB finishB
    finishRelated : ConfigurationBlankTailEq machine finishA finishB

open TransportedRun public

transportExactRun :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {steps : Nat}
    {startA finishA startB : Standard.StandardConfiguration machine}
    (startRelated : ConfigurationBlankTailEq machine startA startB)
    (source : Run.StandardExactRun machine steps startA finishA) →
  TransportedRun startRelated source
transportExactRun startRelated Run.standardRunDone = record
  { finishB = _
  ; target = Run.standardRunDone
  ; finishRelated = startRelated
  }
transportExactRun startRelated
    (Run.standardRunStep edge rest)
  with transportOneStep startRelated edge
... | one
  with transportExactRun (afterRelated one) rest
... | tail = record
  { finishB = finishB tail
  ; target = Run.standardRunStep (targetEdge one) (target tail)
  ; finishRelated = finishRelated tail
  }

------------------------------------------------------------------------
-- Control/scanned coordinates are literally shared by the relation.
------------------------------------------------------------------------

relatedStateExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {left right : Standard.StandardConfiguration machine} →
  ConfigurationBlankTailEq machine left right →
  Standard.state left ≡ Standard.state right
relatedStateExact (configurationEq leftRel rightRel) = refl

relatedScannedExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {left right : Standard.StandardConfiguration machine} →
  ConfigurationBlankTailEq machine left right →
  Standard.scanned left ≡ Standard.scanned right
relatedScannedExact (configurationEq leftRel rightRel) = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Explicit finite far-tail blanks are a representation choice only. They do not
-- change standard control/scanned semantics or exact run length. The remaining
-- bridge is to prove that `guardedStandardStart input T` is blank-tail-equivalent
-- to the canonical minimal start for that same input.
------------------------------------------------------------------------
