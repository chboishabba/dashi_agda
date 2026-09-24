module DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact where

------------------------------------------------------------------------
-- THE ONLY EXTRA INVARIANT NEEDED TO ITERATE THE LOCALITY COMPILER
--
-- A radius-one machine step moves the unique head by at most one cell.
-- We measure the number of cells strictly to the left/right of the unique
-- head directly from the row.  A margin of suc k before a well-formed step
-- gives margin k afterwards.  Margin >= 1 reconstructs the interior-head
-- witness required by the reverse Cook--Levin locality theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _≤_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate

------------------------------------------------------------------------
-- Row-intrinsic head coordinates
------------------------------------------------------------------------

leftOfHead :
  ∀ {State Symbol : Set} →
  List (Local.TapeCell State Symbol) → Nat
leftOfHead [] = zero
leftOfHead (Local.headed state symbol ∷ rest) = zero
leftOfHead (Local.plain symbol ∷ rest) =
  suc (leftOfHead rest)

rightOfHead :
  ∀ {State Symbol : Set} →
  List (Local.TapeCell State Symbol) → Nat
rightOfHead [] = zero
rightOfHead (Local.headed state symbol ∷ rest) =
  Coordinate.listLength rest
rightOfHead (Local.plain symbol ∷ rest) =
  rightOfHead rest

record HeadMargin
    {State Symbol : Set}
    (k : Nat)
    (cells : List (Local.TapeCell State Symbol)) : Set where
  field
    leftMargin  : k ≤ leftOfHead cells
    rightMargin : k ≤ rightOfHead cells

open HeadMargin public

weakenMargin :
  ∀ {State Symbol : Set} {k : Nat}
    {cells : List (Local.TapeCell State Symbol)} →
  HeadMargin (suc k) cells →
  HeadMargin k cells
weakenMargin margin = record
  { leftMargin = NatP.≤-trans (NatP.n≤1+n _) (leftMargin margin)
  ; rightMargin = NatP.≤-trans (NatP.n≤1+n _) (rightMargin margin)
  }

------------------------------------------------------------------------
-- Plain prefixes and suffixes give exact coordinates.
------------------------------------------------------------------------

leftOfHead_appendPlain_head :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {left read right : Symbol}
    {q : State} →
  WF.PlainCells prefix →
  leftOfHead
    (Local.append prefix
      (Local.plain left
        ∷ Local.headed q read
        ∷ Local.plain right
        ∷ suffix))
  ≡ suc (Coordinate.listLength prefix)
leftOfHead_appendPlain_head WF.plainNil =
  refl
leftOfHead_appendPlain_head
    (WF.plainCons plain)
    rewrite leftOfHead_appendPlain_head plain =
  refl

rightOfHead_appendPlain_head :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {left read right : Symbol}
    {q : State} →
  WF.PlainCells prefix →
  rightOfHead
    (Local.append prefix
      (Local.plain left
        ∷ Local.headed q read
        ∷ Local.plain right
        ∷ suffix))
  ≡ suc (Coordinate.listLength suffix)
rightOfHead_appendPlain_head WF.plainNil =
  refl
rightOfHead_appendPlain_head
    (WF.plainCons plain)
    rewrite rightOfHead_appendPlain_head plain =
  refl

leftOfHead_appendPlain_head_left :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {q : State} {a b : Symbol} →
  WF.PlainCells prefix →
  leftOfHead
    (Local.append prefix
      (Local.headed q a
        ∷ Local.plain b
        ∷ Local.plain b
        ∷ suffix))
  ≡ Coordinate.listLength prefix
leftOfHead_appendPlain_head_left WF.plainNil =
  refl
leftOfHead_appendPlain_head_left
    (WF.plainCons plain)
    rewrite leftOfHead_appendPlain_head_left plain =
  refl

rightOfHead_appendPlain_head_left :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {q : State} {a b c : Symbol} →
  WF.PlainCells prefix →
  rightOfHead
    (Local.append prefix
      (Local.headed q a
        ∷ Local.plain b
        ∷ Local.plain c
        ∷ suffix))
  ≡ suc (suc (Coordinate.listLength suffix))
rightOfHead_appendPlain_head_left WF.plainNil =
  refl
rightOfHead_appendPlain_head_left
    (WF.plainCons plain)
    rewrite rightOfHead_appendPlain_head_left plain =
  refl

leftOfHead_appendPlain_head_right :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {q : State} {a b : Symbol} →
  WF.PlainCells prefix →
  leftOfHead
    (Local.append prefix
      (Local.plain a
        ∷ Local.plain b
        ∷ Local.headed q a
        ∷ suffix))
  ≡ suc (suc (Coordinate.listLength prefix))
leftOfHead_appendPlain_head_right WF.plainNil =
  refl
leftOfHead_appendPlain_head_right
    (WF.plainCons plain)
    rewrite leftOfHead_appendPlain_head_right plain =
  refl

rightOfHead_appendPlain_head_right :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {q : State} {a b c : Symbol} →
  WF.PlainCells prefix →
  rightOfHead
    (Local.append prefix
      (Local.plain a
        ∷ Local.plain b
        ∷ Local.headed q c
        ∷ suffix))
  ≡ Coordinate.listLength suffix
rightOfHead_appendPlain_head_right WF.plainNil =
  refl
rightOfHead_appendPlain_head_right
    (WF.plainCons plain)
    rewrite rightOfHead_appendPlain_head_right plain =
  refl

------------------------------------------------------------------------
-- A well-formed radius-one step consumes at most one margin cell.
------------------------------------------------------------------------

wellFormedStepMargin :
  ∀ {machine before after k} →
  (step : WF.WellFormedMachineStep machine before after) →
  HeadMargin (suc k) (Local.cells before) →
  HeadMargin k (Local.cells after)
wellFormedStepMargin {k = k} step margin
    with Local.ruleIsConfigured (WF.step step)
... | Local.realizes-left =
  record
    { leftMargin = leftBound
    ; rightMargin = rightBound
    }
  where
    occ = WF.occurrence (WF.wellFormedOccurrence step)
    pp = WF.prefixPlain (WF.wellFormedOccurrence step)

    hBeforeLeft :
      leftOfHead (Local.cells before)
      ≡ suc (Coordinate.listLength (Local.prefix occ))
    hBeforeLeft
      rewrite Local.beforeShape occ
            | leftOfHead_appendPlain_head pp = refl

    hAfterLeft :
      leftOfHead (Local.cells after)
      ≡ Coordinate.listLength (Local.prefix occ)
    hAfterLeft
      rewrite Local.afterShape occ
            | leftOfHead_appendPlain_head_left pp = refl

    hBeforeRight :
      rightOfHead (Local.cells before)
      ≡ suc (Coordinate.listLength (Local.suffix occ))
    hBeforeRight
      rewrite Local.beforeShape occ
            | rightOfHead_appendPlain_head pp = refl

    hAfterRight :
      rightOfHead (Local.cells after)
      ≡ suc (suc (Coordinate.listLength (Local.suffix occ)))
    hAfterRight
      rewrite Local.afterShape occ
            | rightOfHead_appendPlain_head_left pp = refl

    leftBound : k ≤ leftOfHead (Local.cells after)
    leftBound
      rewrite hAfterLeft =
      NatP.≤-pred
        (substRight hBeforeLeft (leftMargin margin))
      where
        substRight : ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        substRight refl h = h

    rightBound : k ≤ rightOfHead (Local.cells after)
    rightBound
      rewrite hAfterRight =
      NatP.≤-trans
        (NatP.≤-trans
          (NatP.n≤1+n k)
          (NatP.≤-pred
            (substRight hBeforeRight (rightMargin margin))))
        (NatP.n≤1+n _)
      where
        substRight : ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        substRight refl h = h

... | Local.realizes-stay =
  record
    { leftMargin = leftBound
    ; rightMargin = rightBound
    }
  where
    occ = WF.occurrence (WF.wellFormedOccurrence step)
    pp = WF.prefixPlain (WF.wellFormedOccurrence step)

    hBeforeLeft :
      leftOfHead (Local.cells before)
      ≡ suc (Coordinate.listLength (Local.prefix occ))
    hBeforeLeft
      rewrite Local.beforeShape occ
            | leftOfHead_appendPlain_head pp = refl

    hAfterLeft :
      leftOfHead (Local.cells after)
      ≡ suc (Coordinate.listLength (Local.prefix occ))
    hAfterLeft
      rewrite Local.afterShape occ
            | leftOfHead_appendPlain_head pp = refl

    hBeforeRight :
      rightOfHead (Local.cells before)
      ≡ suc (Coordinate.listLength (Local.suffix occ))
    hBeforeRight
      rewrite Local.beforeShape occ
            | rightOfHead_appendPlain_head pp = refl

    hAfterRight :
      rightOfHead (Local.cells after)
      ≡ suc (Coordinate.listLength (Local.suffix occ))
    hAfterRight
      rewrite Local.afterShape occ
            | rightOfHead_appendPlain_head pp = refl

    leftBound : k ≤ leftOfHead (Local.cells after)
    leftBound
      rewrite hAfterLeft =
      NatP.≤-trans
        (NatP.n≤1+n k)
        (NatP.≤-pred
          (substRight hBeforeLeft (leftMargin margin)))
      where
        substRight : ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        substRight refl h = h

    rightBound : k ≤ rightOfHead (Local.cells after)
    rightBound
      rewrite hAfterRight =
      NatP.≤-trans
        (NatP.n≤1+n k)
        (NatP.≤-pred
          (substRight hBeforeRight (rightMargin margin)))
      where
        substRight : ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        substRight refl h = h

... | Local.realizes-right =
  record
    { leftMargin = leftBound
    ; rightMargin = rightBound
    }
  where
    occ = WF.occurrence (WF.wellFormedOccurrence step)
    pp = WF.prefixPlain (WF.wellFormedOccurrence step)

    hBeforeLeft :
      leftOfHead (Local.cells before)
      ≡ suc (Coordinate.listLength (Local.prefix occ))
    hBeforeLeft
      rewrite Local.beforeShape occ
            | leftOfHead_appendPlain_head pp = refl

    hAfterLeft :
      leftOfHead (Local.cells after)
      ≡ suc (suc (Coordinate.listLength (Local.prefix occ)))
    hAfterLeft
      rewrite Local.afterShape occ
            | leftOfHead_appendPlain_head_right pp = refl

    hBeforeRight :
      rightOfHead (Local.cells before)
      ≡ suc (Coordinate.listLength (Local.suffix occ))
    hBeforeRight
      rewrite Local.beforeShape occ
            | rightOfHead_appendPlain_head pp = refl

    hAfterRight :
      rightOfHead (Local.cells after)
      ≡ Coordinate.listLength (Local.suffix occ)
    hAfterRight
      rewrite Local.afterShape occ
            | rightOfHead_appendPlain_head_right pp = refl

    leftBound : k ≤ leftOfHead (Local.cells after)
    leftBound
      rewrite hAfterLeft =
      NatP.≤-trans
        (NatP.≤-pred
          (substRight hBeforeLeft (leftMargin margin)))
        (NatP.≤-trans (NatP.n≤1+n _) (NatP.n≤1+n _))
      where
        substRight : ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        substRight refl h = h

    rightBound : k ≤ rightOfHead (Local.cells after)
    rightBound
      rewrite hAfterRight =
      NatP.≤-pred
        (substRight hBeforeRight (rightMargin margin))
      where
        substRight : ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        substRight refl h = h

------------------------------------------------------------------------
-- Unique head + one cell of margin on each side reconstructs interiority.
------------------------------------------------------------------------

record InteriorCells
    {State Symbol : Set}
    (cells : List (Local.TapeCell State Symbol)) : Set where
  field
    prefix suffix : List (Local.TapeCell State Symbol)
    leftSymbol readSymbol rightSymbol : Symbol
    headState : State
    prefixPlain : WF.PlainCells prefix
    suffixPlain : WF.PlainCells suffix
    shape :
      cells ≡ Local.append prefix
        (Local.plain leftSymbol
          ∷ Local.headed headState readSymbol
          ∷ Local.plain rightSymbol
          ∷ suffix)

open InteriorCells public

interiorCellsFromUniqueMargin :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)} →
  WF.ExactlyOneHead cells →
  HeadMargin 1 cells →
  InteriorCells cells
interiorCellsFromUniqueMargin
    (WF.headHere plain) margin
    with leftMargin margin
... | ()
interiorCellsFromUniqueMargin
    (WF.plainBefore {symbol = left}
      (WF.headHere WF.plainNil)) margin
    with rightMargin margin
... | ()
interiorCellsFromUniqueMargin
    (WF.plainBefore {symbol = left}
      (WF.headHere {state = q} {symbol = read}
        (WF.plainCons {symbol = right} suffixPlain)))
    margin =
  record
    { prefix = []
    ; suffix = _
    ; leftSymbol = left
    ; readSymbol = read
    ; rightSymbol = right
    ; headState = q
    ; prefixPlain = WF.plainNil
    ; suffixPlain = suffixPlain
    ; shape = refl
    }
interiorCellsFromUniqueMargin
    (WF.plainBefore {symbol = first}
      (WF.plainBefore unique))
    margin =
  prepend first
    (interiorCellsFromUniqueMargin unique tailMargin)
  where
    tailMargin : HeadMargin 1 _
    tailMargin = record
      { leftMargin = NatP.≤-pred (leftMargin margin)
      ; rightMargin = rightMargin margin
      }

    prepend :
      ∀ firstSymbol →
      InteriorCells _ →
      InteriorCells _
    prepend firstSymbol interior =
      record
        { prefix = Local.plain firstSymbol ∷ prefix interior
        ; suffix = suffix interior
        ; leftSymbol = leftSymbol interior
        ; readSymbol = readSymbol interior
        ; rightSymbol = rightSymbol interior
        ; headState = headState interior
        ; prefixPlain = WF.plainCons (prefixPlain interior)
        ; suffixPlain = suffixPlain interior
        ; shape = cong (λ xs → Local.plain firstSymbol ∷ xs)
            (shape interior)
        }

interiorExactlyOneHead :
  ∀ {machine row} →
  Character.InteriorHeadConfiguration machine row →
  WF.ExactlyOneHead (Local.cells row)
interiorExactlyOneHead interior =
  WF.transportExactlyOneHead
    (sym (Character.rowShape interior))
    (WF.prependPlain
      (Character.prefixPlain interior)
      (WF.plainBefore
        (WF.headHere
          (WF.plainCons
            (Character.suffixPlain interior)))))


interiorFromUniqueMargin :
  ∀ {machine row} →
  WF.ExactlyOneHead (Local.cells row) →
  HeadMargin 1 (Local.cells row) →
  Character.InteriorHeadConfiguration machine row
interiorFromUniqueMargin unique margin
    with interiorCellsFromUniqueMargin unique margin
... | interior =
  record
    { Character.prefix = prefix interior
    ; Character.suffix = suffix interior
    ; Character.leftSymbol = leftSymbol interior
    ; Character.readSymbol = readSymbol interior
    ; Character.rightSymbol = rightSymbol interior
    ; Character.headState = headState interior
    ; Character.prefixPlain = prefixPlain interior
    ; Character.suffixPlain = suffixPlain interior
    ; Character.rowShape = shape interior
    }

afterInteriorOfMargin :
  ∀ {machine before after} →
  (step : WF.WellFormedMachineStep machine before after) →
  HeadMargin 2 (Local.cells before) →
  Character.InteriorHeadConfiguration machine after
afterInteriorOfMargin step margin =
  interiorFromUniqueMargin
    (WF.afterExactlyOneHead step)
    (wellFormedStepMargin step margin)
