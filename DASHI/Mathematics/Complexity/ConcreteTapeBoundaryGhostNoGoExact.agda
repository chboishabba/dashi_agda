{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.ConcreteTapeBoundaryGhostNoGoExact where

------------------------------------------------------------------------
-- REAL COUNTEREXAMPLE TO A TOO-STRONG GLOBAL WINDOW IMPLICATION.
--
-- Original owners:
-- ConcreteTapeMachineLocalityExact: original TapeCell / TapeRule carriers.
-- ConcreteTapeWellFormedConfigurationExact: original ExactlyOneHead.
-- ConcreteTapeLocalWindowPatternsExact: original seven applicable right-move
-- pattern constructors (documented below; the currently failing module is
-- deliberately NOT imported into this independent no-go checker).
--
-- Positions 0..8. The original old head at position 5 is interior:
-- old = P P P P P H(q,a) P P P
-- new = H(q',a) P P P P P H(q',a) P P
--
-- Every aligned width-three pair is one of the actual source patterns:
-- at 0 right-overlap-plus-two (a phantom at the left row boundary);
-- at 1,2 legal-unchanged;
-- at 3 right-overlap-minus-one;
-- at 4 legal-centered (Local.realizes-right);
-- at 5 right-overlap-plus-one;
-- at 6 right-overlap-plus-two (genuine movement).
--
-- Hence unrestricted legal windows + unique interior before head DO NOT
-- imply a unique after head. This module checks the same original row
-- carrier and original head predicate, and provides an independent
-- constructive contradiction to the claimed conclusion.
--
-- NO imported source status bit, postulate or unsafe termination is used.
-- Compile under Agda 2.9 --safe to accept this finite no-go certificate.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF

module Ghost
    (machine : Local.ConcreteTapeMachine)
    (q q' : Local.State machine)
    (a : Local.Symbol machine) where

  Cell : Set
  Cell = Local.TapeCell (Local.State machine) (Local.Symbol machine)

  p : Cell
  p = Local.plain a

  oldCells : List Cell
  oldCells =
    p ∷ p ∷ p ∷ p ∷ p ∷ Local.headed q a ∷ p ∷ p ∷ p ∷ []

  newCells : List Cell
  newCells =
    Local.headed q' a ∷ p ∷ p ∷ p ∷ p ∷ p ∷
      Local.headed q' a ∷ p ∷ p ∷ []

  -- Original well-formedness: the old row has exactly one head.
  oldExactlyOneHead : WF.ExactlyOneHead oldCells
  oldExactlyOneHead =
    WF.plainBefore
      (WF.plainBefore
        (WF.plainBefore
          (WF.plainBefore
            (WF.plainBefore
              (WF.headHere
                (WF.plainCons
                  (WF.plainCons WF.plainNil))))))

  -- After the first new head, the trailing second head is not plain.
  -- This is refuted by the ACTUAL WF.PlainCells constructors.
  trailingHeadIsNotPlain :
    WF.PlainCells
      (p ∷ p ∷ p ∷ p ∷ p ∷ Local.headed q' a ∷ p ∷ p ∷ []) →
    ⊥
  trailingHeadIsNotPlain
    (WF.plainCons
      (WF.plainCons
        (WF.plainCons
          (WF.plainCons
            (WF.plainCons ())))))

  -- The original WF.ExactlyOneHead cannot be inhabited for this new row.
  newNotExactlyOneHead : WF.ExactlyOneHead newCells → ⊥
  newNotExactlyOneHead (WF.headHere suffixPlain) =
    trailingHeadIsNotPlain suffixPlain

  -- The CENTERED right-moving window itself is genuinely configured.
  centralMoveIsOriginalRule :
    Local.RuleRealizesWindow machine
      (Local.tape-rule q a q' a Local.moveRight)
      (Local.six-cell-window
        p (Local.headed q a) p
        p p (Local.headed q' a))
  centralMoveIsOriginalRule = Local.realizes-right

  -- A left-moving centered pattern explicitly disproves the discarded
  -- claim 'oldLeft is plain -> newLeft is plain' even in one window.
  centralLeftMoveHasHeadedNewLeft :
    Local.RuleRealizesWindow machine
      (Local.tape-rule q a q' a Local.moveLeft)
      (Local.six-cell-window
        p (Local.headed q a) p
        (Local.headed q' a) p p)
  centralLeftMoveHasHeadedNewLeft = Local.realizes-left
