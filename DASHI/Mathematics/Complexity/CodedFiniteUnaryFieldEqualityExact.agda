module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityExact where

------------------------------------------------------------------------
-- CONSTANT-CONTROL EQUALITY MICROCODE FOR TWO UNARY FIELDS
--
-- Tape shape at entry:
--
--   blank | true^m false true^n false | blank...
--           ^ head
--
-- This owner exposes only literal finite rules.  It deliberately does not
-- manufacture a `CodedFiniteStandardTM` until dispatch uniqueness and the whole
-- equality run theorem are proved in the ordinary rule semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

stateCount : Nat
stateCount = 7

symbolCount : Nat
symbolCount = 5

findFirst seekSecond findSecond returnLeft checkSecond equalState unequalState :
  Fin.Fin stateCount
findFirst = Fin.zero
seekSecond = Fin.suc Fin.zero
findSecond = Fin.suc (Fin.suc Fin.zero)
returnLeft = Fin.suc (Fin.suc (Fin.suc Fin.zero))
checkSecond = Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
equalState = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
unequalState =
  Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

blank trueBit terminator markedFirst markedSecond : Fin.Fin symbolCount
blank = Fin.zero
trueBit = Fin.suc Fin.zero
terminator = Fin.suc (Fin.suc Fin.zero)
markedFirst = Fin.suc (Fin.suc (Fin.suc Fin.zero))
markedSecond = Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

rule :
  Fin.Fin stateCount → Fin.Fin symbolCount →
  Fin.Fin stateCount → Fin.Fin symbolCount → Local.Direction →
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rule = Local.tape-rule

rFFmark rFFtrue rFFend :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFFmark = rule findFirst markedFirst findFirst markedFirst Local.moveRight
rFFtrue = rule findFirst trueBit seekSecond markedFirst Local.moveRight
rFFend = rule findFirst terminator checkSecond terminator Local.moveRight

rSStrue rSSmark rSSend :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rSStrue = rule seekSecond trueBit seekSecond trueBit Local.moveRight
rSSmark = rule seekSecond markedFirst seekSecond markedFirst Local.moveRight
rSSend = rule seekSecond terminator findSecond terminator Local.moveRight

rFSmark rFStrue rFSend :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFSmark = rule findSecond markedSecond findSecond markedSecond Local.moveRight
rFStrue = rule findSecond trueBit returnLeft markedSecond Local.moveLeft
rFSend = rule findSecond terminator unequalState terminator Local.stayPut

rRLtrue rRLend rRLm1 rRLm2 rRLblank :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rRLtrue = rule returnLeft trueBit returnLeft trueBit Local.moveLeft
rRLend = rule returnLeft terminator returnLeft terminator Local.moveLeft
rRLm1 = rule returnLeft markedFirst returnLeft markedFirst Local.moveLeft
rRLm2 = rule returnLeft markedSecond returnLeft markedSecond Local.moveLeft
rRLblank = rule returnLeft blank findFirst blank Local.moveRight

rCSmark rCStrue rCSend :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rCSmark = rule checkSecond markedSecond checkSecond markedSecond Local.moveRight
rCStrue = rule checkSecond trueBit unequalState trueBit Local.stayPut
rCSend = rule checkSecond terminator equalState terminator Local.stayPut

rules : List (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount))
rules =
  rFFmark ∷ rFFtrue ∷ rFFend ∷
  rSStrue ∷ rSSmark ∷ rSSend ∷
  rFSmark ∷ rFStrue ∷ rFSend ∷
  rRLtrue ∷ rRLend ∷ rRLm1 ∷ rRLm2 ∷ rRLblank ∷
  rCSmark ∷ rCStrue ∷ rCSend ∷ []

record UnaryFieldEqualityMicrocode : Set where
  constructor unary-field-equality-microcode
  field
    literalRules :
      List (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount))
    equalSink : Fin.Fin stateCount
    unequalSink : Fin.Fin stateCount

microcode : UnaryFieldEqualityMicrocode
microcode = unary-field-equality-microcode rules equalState unequalState

------------------------------------------------------------------------
-- LIVE PAYMENT
--
-- Literal constant-control mark/shuttle rules are present.  Still required:
--   * finite dispatch-uniqueness proof for this exact list;
--   * exact runs proving true^m/true^n reaches equal iff m=n;
--   * restoration/cleanup policy for the temporary mark symbols if the caller
--     needs the input preserved.
------------------------------------------------------------------------
