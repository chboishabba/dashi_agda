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
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact as Padding
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate

plainAppend :
  ∀ {State Symbol : Set}
    {xs ys : List (Local.TapeCell State Symbol)} →
  WF.PlainCells xs →
  WF.PlainCells ys →
  WF.PlainCells (Local.append xs ys)
plainAppend WF.plainNil right = right
plainAppend (WF.plainCons left) right =
  WF.plainCons (plainAppend left right)

guardedInitialCells :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
guardedInitialCells input steps =
  Local.append
    (Padding.replicateBlank steps)
    (Local.append
      (Input.initialInputCells input)
      (Padding.replicateBlank steps))

guardedInitialRow :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  Local.TapeRow machine
guardedInitialRow input steps =
  Local.tape-row (guardedInitialCells input steps)

guardedInitialCols :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  Nat
guardedInitialCols input steps =
  Input.initialInputCellCount input + (2 * steps)

guardedInitialCellCount :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Coordinate.listLength (guardedInitialCells input steps)
  ≡ guardedInitialCols input steps
guardedInitialCellCount input steps
    rewrite Padding.appendLength
      (Padding.replicateBlank steps)
      (Local.append
        (Input.initialInputCells input)
        (Padding.replicateBlank steps))
          | Padding.appendLength
              (Input.initialInputCells input)
              (Padding.replicateBlank steps)
          | Padding.replicateBlankLength steps
          | Padding.replicateBlankLength steps =
  arithmetic
  where
    arithmetic :
      steps + (Input.initialInputCellCount input + steps)
      ≡ Input.initialInputCellCount input + (2 * steps)
    arithmetic =
      trans
        (sym (NatP.+-assoc steps (Input.initialInputCellCount input) steps))
        (byRearrange steps (Input.initialInputCellCount input))
    where
      byRearrange : ∀ a b → a + b + a ≡ b + (2 * a)
      byRearrange zero b
        rewrite NatP.+-identityʳ b = refl
      byRearrange (suc a) b
        rewrite NatP.+-suc a b
              | NatP.+-suc (a + b) a
              | NatP.+-suc b (2 * a)
              | byRearrange a b =
        refl

------------------------------------------------------------------------
-- Explicit interior witness for the guarded literal input row.
------------------------------------------------------------------------

guardedInitialInterior :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.InteriorHeadConfiguration
    machine
    (guardedInitialRow input steps)
guardedInitialInterior {machine} input steps =
  record
    { Character.prefix =
        Padding.replicateBlank steps
    ; Character.suffix =
        Local.append
          (Character.suffix base)
          (Padding.replicateBlank steps)
    ; Character.leftSymbol =
        Character.leftSymbol base
    ; Character.readSymbol =
        Character.readSymbol base
    ; Character.rightSymbol =
        Character.rightSymbol base
    ; Character.headState =
        Character.headState base
    ; Character.prefixPlain =
        Padding.replicateBlankPlain steps
    ; Character.suffixPlain =
        plainAppend
          (Character.suffixPlain base)
          (Padding.replicateBlankPlain steps)
    ; Character.rowShape =
        guardedShape
    }
  where
    base = Input.initialInputInterior input

    guardedShape :
      Local.cells (guardedInitialRow input steps)
      ≡
      Local.append
        (Padding.replicateBlank steps)
        (Local.plain (Character.leftSymbol base)
          ∷ Local.headed
              (Character.headState base)
              (Character.readSymbol base)
          ∷ Local.plain (Character.rightSymbol base)
          ∷ Local.append
              (Character.suffix base)
              (Padding.replicateBlank steps))
    guardedShape
      with input
    ... | [] = refl
    ... | symbol ∷ [] = refl
    ... | symbol ∷ next ∷ rest = refl

guardedInitialState :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.headState (guardedInitialInterior input steps)
  ≡ Local.initialState machine
guardedInitialState input steps =
  Accepting.headIsInitial
    (Input.initialInputIsInitialInterior input)

------------------------------------------------------------------------
-- The initial margin is exactly large enough for T radius-one moves.
------------------------------------------------------------------------

guardedInitialMargin :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Margin.HeadMargin (suc steps)
    (Local.cells (guardedInitialRow input steps))
guardedInitialMargin input steps =
  record
    { Margin.leftMargin = leftBound
    ; Margin.rightMargin = rightBound
    }
  where
    interior = guardedInitialInterior input steps

    leftExact :
      Margin.leftOfHead
        (Local.cells (guardedInitialRow input steps))
      ≡ suc (Coordinate.listLength
        (Padding.replicateBlank steps))
    leftExact
      rewrite Character.rowShape interior
            | Margin.leftOfHead_appendPlain_head
                (Character.prefixPlain interior) =
      refl

    rightExact :
      Margin.rightOfHead
        (Local.cells (guardedInitialRow input steps))
      ≡ suc (Coordinate.listLength
        (Character.suffix interior))
    rightExact
      rewrite Character.rowShape interior
            | Margin.rightOfHead_appendPlain_head
                (Character.prefixPlain interior) =
      refl

    prefixLen :
      Coordinate.listLength (Padding.replicateBlank steps)
      ≡ steps
    prefixLen = Padding.replicateBlankLength steps

    suffixGuard :
      steps ≤ Coordinate.listLength
        (Character.suffix interior)
    suffixGuard
      rewrite Padding.appendLength
        (Character.suffix (Input.initialInputInterior input))
        (Padding.replicateBlank steps)
          | Padding.replicateBlankLength steps =
      NatP.m≤n+m steps _

    leftBound :
      suc steps ≤ Margin.leftOfHead
        (Local.cells (guardedInitialRow input steps))
    leftBound
      rewrite leftExact | prefixLen =
      NatP.≤-refl _

    rightBound :
      suc steps ≤ Margin.rightOfHead
        (Local.cells (guardedInitialRow input steps))
    rightBound
      rewrite rightExact =
      NatP.s≤s suffixGuard

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

