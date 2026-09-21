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
    prefixPlain = WF.prefixPlain (WF.wellFormedOccurrence step)
    suffixPlain = WF.suffixPlain (WF.wellFormedOccurrence step)

    beforeLeft :
      leftOfHead (Local.cells _) ≡
        suc (Coordinate.listLength (Local.prefix occ))
    beforeLeft
      rewrite Local.beforeShape occ
            | leftOfHead_appendPlain_head prefixPlain =
      refl

    afterLeft :
      leftOfHead (Local.cells _) ≡
        Coordinate.listLength (Local.prefix occ)
    afterLeft
      rewrite Local.afterShape occ
            | leftOfHead_appendPlain_head_left prefixPlain =
      refl

    leftBound : k ≤ leftOfHead (Local.cells _)
    leftBound
      rewrite afterLeft =
      NatP.s≤s-injective
        (NatP.≤-trans
          (NatP.s≤s (NatP.≤-refl k))
          (subst≤ beforeLeft (leftMargin margin)))
      where
        subst≤ :
          ∀ {a b c : Nat} → a ≡ b → c ≤ a → c ≤ b
        subst≤ refl h = h

    rightBound : k ≤ rightOfHead (Local.cells _)
    rightBound =
      NatP.≤-trans
        (NatP.n≤1+n k)
        (NatP.≤-trans
          (NatP.n≤1+n (suc k))
          (transportRight (rightMargin margin)))
      where
        transportRight :
          suc k ≤ rightOfHead (Local.cells before) →
          suc (suc k) ≤ rightOfHead (Local.cells after)
        transportRight h
          rewrite Local.beforeShape occ
                | Local.afterShape occ
                | rightOfHead_appendPlain_head prefixPlain
                | rightOfHead_appendPlain_head_left prefixPlain =
          NatP.s≤s h

... | Local.realizes-stay =
  record
    { leftMargin =
        NatP.≤-trans (NatP.n≤1+n k)
          (NatP.≤-trans
            (leftMargin margin)
            (sameLeft refl))
    ; rightMargin =
        NatP.≤-trans (NatP.n≤1+n k)
          (NatP.≤-trans
            (rightMargin margin)
            (sameRight refl))
    }
  where
    occ = WF.occurrence (WF.wellFormedOccurrence step)

    sameLeft :
      leftOfHead (Local.cells before) ≡
      leftOfHead (Local.cells after) →
      leftOfHead (Local.cells before) ≤
      leftOfHead (Local.cells after)
    sameLeft refl = NatP.≤-refl _

    sameRight :
      rightOfHead (Local.cells before) ≡
      rightOfHead (Local.cells after) →
      rightOfHead (Local.cells before) ≤
      rightOfHead (Local.cells after)
    sameRight refl = NatP.≤-refl _

... | Local.realizes-right =
  record
    { leftMargin =
        NatP.≤-trans
          (NatP.n≤1+n k)
          (transportLeft (leftMargin margin))
    ; rightMargin = rightBound
    }
  where
    occ = WF.occurrence (WF.wellFormedOccurrence step)
    prefixPlain = WF.prefixPlain (WF.wellFormedOccurrence step)

    transportLeft :
      suc k ≤ leftOfHead (Local.cells before) →
      suc k ≤ leftOfHead (Local.cells after)
    transportLeft h
      rewrite Local.beforeShape occ
            | Local.afterShape occ
            | leftOfHead_appendPlain_head prefixPlain
            | leftOfHead_appendPlain_head_right prefixPlain =
      NatP.≤-trans h (NatP.n≤1+n _)

    rightBound : k ≤ rightOfHead (Local.cells after)
    rightBound
      rewrite Local.beforeShape occ
            | Local.afterShape occ
            | rightOfHead_appendPlain_head prefixPlain
            | rightOfHead_appendPlain_head_right prefixPlain =
      NatP.s≤s-injective (rightMargin margin)

------------------------------------------------------------------------
-- Unique head + one cell of margin on each side reconstructs interiority.
------------------------------------------------------------------------

interiorFromUniqueMargin :
  ∀ {machine row} →
  WF.ExactlyOneHead (Local.cells row) →
  HeadMargin 1 (Local.cells row) →
  Character.InteriorHeadConfiguration machine row
interiorFromUniqueMargin {row = row}
    (WF.headHere plain) margin =
  ⊥-elim (NatP.1+n≰n 0 (leftMargin margin))
interiorFromUniqueMargin {machine} {row}
    (WF.plainBefore (WF.headHere WF.plainNil)) margin =
  ⊥-elim (NatP.1+n≰n 0 (rightMargin margin))
interiorFromUniqueMargin {machine} {row}
    (WF.plainBefore (WF.headHere (WF.plainCons suffixPlain))) margin =
  record
    { Character.prefix = []
    ; Character.suffix = suffix
    ; Character.leftSymbol = leftSymbol
    ; Character.readSymbol = readSymbol
    ; Character.rightSymbol = rightSymbol
    ; Character.headState = headState
    ; Character.prefixPlain = WF.plainNil
    ; Character.suffixPlain = suffixPlain
    ; Character.rowShape = refl
    }
  where
    leftSymbol = _
    readSymbol = _
    rightSymbol = _
    headState = _
    suffix = _
interiorFromUniqueMargin {machine} {row}
    (WF.plainBefore
      (WF.plainBefore unique)) margin =
  prependInterior
    (interiorFromUniqueMargin unique tailMargin)
  where
    tailMargin : HeadMargin 1 _
    tailMargin = record
      { leftMargin = NatP.s≤s-injective (leftMargin margin)
      ; rightMargin = rightMargin margin
      }

    prependInterior :
      ∀ {cellsTail}
        {tailRow : Local.TapeRow machine} →
      Character.InteriorHeadConfiguration machine tailRow →
      Character.InteriorHeadConfiguration machine row
    prependInterior interior =
      record
        { Character.prefix =
            _ ∷ Character.prefix interior
        ; Character.suffix =
            Character.suffix interior
        ; Character.leftSymbol =
            Character.leftSymbol interior
        ; Character.readSymbol =
            Character.readSymbol interior
        ; Character.rightSymbol =
            Character.rightSymbol interior
        ; Character.headState =
            Character.headState interior
        ; Character.prefixPlain =
            WF.plainCons (Character.prefixPlain interior)
        ; Character.suffixPlain =
            Character.suffixPlain interior
        ; Character.rowShape =
            cong (λ xs → _ ∷ xs) (Character.rowShape interior)
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

