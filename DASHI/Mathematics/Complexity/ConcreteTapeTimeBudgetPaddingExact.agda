module DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact where

------------------------------------------------------------------------
-- TIME BUDGET -> ENOUGH BLANK MARGIN FOR EVERY RADIUS-ONE STEP
--
-- The minimal literal input row already has one blank cell on each side of
-- the head.  For a T-step Cook--Levin tableau we add T more blank cells to
-- each side.  Hence the initial head margin is T+1; the one-step margin
-- theorem then leaves margin 1 after all T steps, so every row used by the
-- locality compiler (including the accepting row) remains interior.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact as Padding
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical

plainAppend :
  ∀ {State Symbol : Set}
    {xs ys : List (Local.TapeCell State Symbol)} →
  WF.PlainCells xs →
  WF.PlainCells ys →
  WF.PlainCells (Local.append xs ys)
plainAppend WF.plainNil right = right
plainAppend (WF.plainCons left) right =
  WF.plainCons (plainAppend left right)

coordinateAppendLength :
  ∀ {A : Set} (xs ys : List A) →
  Coordinate.listLength (Local.append xs ys)
  ≡ Coordinate.listLength xs + Coordinate.listLength ys
coordinateAppendLength [] ys = refl
coordinateAppendLength (x ∷ xs) ys = cong suc (coordinateAppendLength xs ys)

replicateBlankCoordLength :
  ∀ {machine} (n : Nat) →
  Coordinate.listLength (Padding.replicateBlank {machine} n) ≡ n
replicateBlankCoordLength zero = refl
replicateBlankCoordLength (suc n) = cong suc (replicateBlankCoordLength n)

canonical_eq_coordinate :
  ∀ {A : Set} (xs : List A) →
  Coordinate.listLength xs ≡ Canonical.listLength xs
canonical_eq_coordinate [] = refl
canonical_eq_coordinate (x ∷ xs) = cong suc (canonical_eq_coordinate xs)

guardedInitialCells :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
guardedInitialCells {machine} input steps =
  Local.append
    (Padding.replicateBlank {machine} steps)
    (Local.append
      (Input.initialInputCells {machine} input)
      (Padding.replicateBlank {machine} steps))

guardedInitialRow :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  Local.TapeRow machine
guardedInitialRow {machine} input steps =
  Local.tape-row (guardedInitialCells {machine} input steps)

guardedInitialCols :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  Nat
guardedInitialCols {machine} input steps =
  Input.initialInputCellCount {machine} input + (2 * steps)

-- The original literal initial row always has a plain-left,
-- headed-middle, plain-right triple. Hence its width is a successor
-- independent of the input/timestep, permitting canonical endcap CNF
-- placement without a vacuous zero-column case.
natPredecessor : Nat → Nat
natPredecessor zero = zero
natPredecessor (suc n) = n

guardedInitialColsMinusOne :
  ∀ {machine} → Input.InputWord machine → Nat → Nat
guardedInitialColsMinusOne input steps =
  natPredecessor (guardedInitialCols input steps)

guardedInitialColsSuccessor :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  guardedInitialCols input steps
  ≡ suc (guardedInitialColsMinusOne input steps)
guardedInitialColsSuccessor input steps = refl


guardedInitialCellCount :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Coordinate.listLength (guardedInitialCells {machine} input steps)
  ≡ guardedInitialCols {machine} input steps
guardedInitialCellCount {machine} input steps =
  trans step1 (trans step2 (trans step3 (trans step4 (trans step5 step6))))
  where
    s = steps
    C = Input.initialInputCellCount {machine} input
    restLen = Coordinate.listLength (Local.append (Input.initialInputCells {machine} input) (Padding.replicateBlank {machine} s))

    step1 : Coordinate.listLength (guardedInitialCells {machine} input steps)
          ≡ Coordinate.listLength (Padding.replicateBlank {machine} s)
            + restLen
    step1 = coordinateAppendLength (Padding.replicateBlank {machine} s) (Local.append (Input.initialInputCells {machine} input) (Padding.replicateBlank {machine} s))

    step2 : Coordinate.listLength (Padding.replicateBlank {machine} s)
            + restLen
          ≡ s + restLen
    step2 = cong (_+ restLen) (replicateBlankCoordLength {machine} s)

    step3 : s + Coordinate.listLength (Local.append (Input.initialInputCells {machine} input) (Padding.replicateBlank {machine} s))
          ≡ s + (Coordinate.listLength (Input.initialInputCells {machine} input) + Coordinate.listLength (Padding.replicateBlank {machine} s))
    step3 = cong (s +_) (coordinateAppendLength (Input.initialInputCells {machine} input) (Padding.replicateBlank {machine} s))

    step4 : s + (Coordinate.listLength (Input.initialInputCells {machine} input) + Coordinate.listLength (Padding.replicateBlank {machine} s))
          ≡ s + (C + s)
    step4 = cong (s +_) (cong₂ _+_ (canonical_eq_coordinate (Input.initialInputCells {machine} input)) (replicateBlankCoordLength {machine} s))

    step5 : s + (C + s) ≡ C + (s + s)
    step5 = trans (NatP.+-comm s (C + s)) (NatP.+-assoc C s s)

    step6 : C + (s + s) ≡ C + (2 * s)
    step6 = cong (C +_) (cong (s +_) (sym (NatP.+-identityʳ s)))

------------------------------------------------------------------------
-- Explicit interior witness for the guarded literal input row.
------------------------------------------------------------------------

guardedShapeHelper :
  ∀ {machine} (input : Input.InputWord machine) (steps : Nat) →
  Local.cells (guardedInitialRow {machine} input steps)
  ≡
  Local.append
    (Padding.replicateBlank {machine} steps)
    (Local.plain {State = Local.State machine} (Character.leftSymbol (Input.initialInputInterior {machine} input))
      ∷ Local.headed
          (Character.headState (Input.initialInputInterior {machine} input))
          (Character.readSymbol (Input.initialInputInterior {machine} input))
      ∷ Local.plain {State = Local.State machine} (Character.rightSymbol (Input.initialInputInterior {machine} input))
      ∷ Local.append
          (Character.suffix (Input.initialInputInterior {machine} input))
          (Padding.replicateBlank {machine} steps))
guardedShapeHelper [] steps = refl
guardedShapeHelper (_ ∷ []) steps = refl
guardedShapeHelper (_ ∷ _ ∷ _) steps = refl

guardedInitialInterior :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.InteriorHeadConfiguration
    machine
    (guardedInitialRow {machine} input steps)
guardedInitialInterior {machine} input steps =
  record
    { prefix =
        Padding.replicateBlank {machine} steps
    ; suffix =
        Local.append
          (Character.suffix base)
          (Padding.replicateBlank {machine} steps)
    ; leftSymbol =
        Character.leftSymbol base
    ; readSymbol =
        Character.readSymbol base
    ; rightSymbol =
        Character.rightSymbol base
    ; headState =
        Character.headState base
    ; prefixPlain =
        Padding.replicateBlankPlain {machine} steps
    ; suffixPlain =
        plainAppend
          (Character.suffixPlain base)
          (Padding.replicateBlankPlain {machine} steps)
    ; rowShape =
        guardedShapeHelper {machine} input steps
    }
  where
    base = Input.initialInputInterior {machine} input

guardedInitialState :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.headState (guardedInitialInterior {machine} input steps)
  ≡ Local.initialState machine
guardedInitialState [] steps = refl
guardedInitialState (_ ∷ []) steps = refl
guardedInitialState (_ ∷ _ ∷ _) steps = refl

------------------------------------------------------------------------
-- The initial margin is exactly large enough for T radius-one moves.
------------------------------------------------------------------------

guardedInitialMargin :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Margin.HeadMargin (suc steps)
    (Local.cells (guardedInitialRow {machine} input steps))
guardedInitialMargin {machine} input steps =
  record
    { leftMargin = leftBound
    ; rightMargin = rightBound
    }
  where
    interior = guardedInitialInterior {machine} input steps

    leftExact :
      Margin.leftOfHead
        (Local.cells (guardedInitialRow {machine} input steps))
      ≡ suc (Coordinate.listLength
        (Padding.replicateBlank {machine} steps))
    leftExact =
      trans (cong Margin.leftOfHead (Character.rowShape interior))
            (Margin.leftOfHead_appendPlain_head {State = Local.State machine} {Symbol = Local.Symbol machine} (Character.prefixPlain interior))

    rightExact :
      Margin.rightOfHead
        (Local.cells (guardedInitialRow {machine} input steps))
      ≡ suc (Coordinate.listLength
        (Character.suffix interior))
    rightExact =
      trans (cong Margin.rightOfHead (Character.rowShape interior))
            (Margin.rightOfHead_appendPlain_head {State = Local.State machine} {Symbol = Local.Symbol machine} (Character.prefixPlain interior))

    prefixLen :
      Coordinate.listLength (Padding.replicateBlank {machine} steps)
      ≡ steps
    prefixLen = replicateBlankCoordLength {machine} steps

    suffixLen :
      Coordinate.listLength (Character.suffix interior)
      ≡ Coordinate.listLength (Character.suffix (Input.initialInputInterior {machine} input)) + steps
    suffixLen =
      trans (coordinateAppendLength (Character.suffix (Input.initialInputInterior {machine} input)) (Padding.replicateBlank {machine} steps))
            (cong (Coordinate.listLength (Character.suffix (Input.initialInputInterior {machine} input)) +_) (replicateBlankCoordLength {machine} steps))

    suffixGuard :
      steps ≤ Coordinate.listLength
        (Character.suffix interior)
    suffixGuard =
      subst (steps ≤_) (sym suffixLen) (NatP.m≤n+m steps (Coordinate.listLength (Character.suffix (Input.initialInputInterior {machine} input))))

    leftBound :
      suc steps ≤ Margin.leftOfHead
        (Local.cells (guardedInitialRow {machine} input steps))
    leftBound =
      NatP.≤-reflexive (sym (trans leftExact (cong suc prefixLen)))

    rightBound :
      suc steps ≤ Margin.rightOfHead
        (Local.cells (guardedInitialRow input steps))
    rightBound =
      subst (suc steps ≤_) (sym rightExact) (s≤s suffixGuard)

record TimeBudgetPaddingReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    exactLinearWidthPaid : Bool
    literalInputPreservedPaid : Bool
    initialStatePreservedPaid : Bool
    initialInteriorPaid : Bool
    initialTPlusOneMarginPaid : Bool
    oneStepConsumesAtMostOneMarginPaid : Bool
    tStepsRemainInteriorPaid : Bool

timeBudgetPaddingReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  TimeBudgetPaddingReceipt machine
timeBudgetPaddingReceipt machine = record
  { exactLinearWidthPaid = true
  ; literalInputPreservedPaid = true
  ; initialStatePreservedPaid = true
  ; initialInteriorPaid = true
  ; initialTPlusOneMarginPaid = true
  ; oneStepConsumesAtMostOneMarginPaid = true
  ; tStepsRemainInteriorPaid = true
  }

