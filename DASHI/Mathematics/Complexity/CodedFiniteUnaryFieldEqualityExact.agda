module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityExact where

------------------------------------------------------------------------
-- CONSTANT-CONTROL EQUALITY FOR TWO SELF-DELIMITING UNARY FIELDS
--
-- Tape shape at entry:
--
--   blank | true^m false true^n false | blank...
--           ^ head
--
-- The machine repeatedly marks one first-field payload bit and one second-field
-- payload bit, shuttling back to the left blank.  When the first field is
-- exhausted it checks that no unmatched second-field bit remains.  Equal and
-- unequal sinks have no resident rules.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded

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

-- findFirst: skip previously marked first bits, or consume a fresh one.
rFFmark : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFFmark = rule findFirst markedFirst findFirst markedFirst Local.moveRight

rFFtrue : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFFtrue = rule findFirst trueBit seekSecond markedFirst Local.moveRight

-- First field exhausted: enter second-field residual check just to the right.
rFFend : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFFend = rule findFirst terminator checkSecond terminator Local.moveRight

-- seekSecond: move to first delimiter, then enter second field.
rSStrue : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rSStrue = rule seekSecond trueBit seekSecond trueBit Local.moveRight

rSSmark : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rSSmark = rule seekSecond markedFirst seekSecond markedFirst Local.moveRight

rSSend : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rSSend = rule seekSecond terminator findSecond terminator Local.moveRight

-- findSecond: skip matched bits; match one fresh bit or fail on delimiter.
rFSmark : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFSmark = rule findSecond markedSecond findSecond markedSecond Local.moveRight

rFStrue : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFStrue = rule findSecond trueBit returnLeft markedSecond Local.moveLeft

rFSend : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rFSend = rule findSecond terminator unequalState terminator Local.stayPut

-- returnLeft: every nonblank code symbol is crossed leftward.  The left blank
-- boundary re-enters findFirst at the first field.
rRLtrue : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rRLtrue = rule returnLeft trueBit returnLeft trueBit Local.moveLeft

rRLend : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rRLend = rule returnLeft terminator returnLeft terminator Local.moveLeft

rRLm1 : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rRLm1 = rule returnLeft markedFirst returnLeft markedFirst Local.moveLeft

rRLm2 : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rRLm2 = rule returnLeft markedSecond returnLeft markedSecond Local.moveLeft

rRLblank : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rRLblank = rule returnLeft blank findFirst blank Local.moveRight

-- checkSecond: all payload must already be marked.
rCSmark : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rCSmark = rule checkSecond markedSecond checkSecond markedSecond Local.moveRight

rCStrue : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rCStrue = rule checkSecond trueBit unequalState trueBit Local.stayPut

rCSend : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
rCSend = rule checkSecond terminator equalState terminator Local.stayPut

rules : List (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount))
rules =
  rFFmark ∷ rFFtrue ∷ rFFend ∷
  rSStrue ∷ rSSmark ∷ rSSend ∷
  rFSmark ∷ rFStrue ∷ rFSend ∷
  rRLtrue ∷ rRLend ∷ rRLm1 ∷ rRLm2 ∷ rRLblank ∷
  rCSmark ∷ rCStrue ∷ rCSend ∷ []

------------------------------------------------------------------------
-- Keys are visibly unique: each state block lists distinct read symbols.
-- A small local key classifier makes the proof independent of rule order.
------------------------------------------------------------------------

keyCode :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount) → Nat
keyCode r =
  Fin.toℕ (Local.sourceState r) * symbolCount + Fin.toℕ (Local.readSymbol r)

-- Rather than hide dispatch in an extensional function, expose the finite rule
-- table and use an explicit proof by occurrence cases.  The cases are verbose
-- but finite and mechanically inspectable.
postulate-free-dispatch-note : Set
postulate-free-dispatch-note = ⊤
  where
    open import Agda.Builtin.Unit using (⊤)

------------------------------------------------------------------------
-- Dispatch proof is factored through source/read equality plus the fact that
-- every listed key is distinct.  `listedKeyUnique` is proved by finite inversion
-- in the companion validation/closure tranche; until then this module exports
-- the literal microcode only and does not manufacture a CodedFiniteStandardTM.
------------------------------------------------------------------------

record UnaryFieldEqualityMicrocode : Set where
  constructor unary-field-equality-microcode
  field
    literalRules : List (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount))
    equalSink : Fin.Fin stateCount
    unequalSink : Fin.Fin stateCount

microcode : UnaryFieldEqualityMicrocode
microcode = unary-field-equality-microcode rules equalState unequalState

------------------------------------------------------------------------
-- Sink quiescence is already exact independently of the pending finite key
-- inversion proof.
------------------------------------------------------------------------

equalSinkCannotBeSource :
  (r : Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)) →
  Local.sourceState r ≡ equalState →
  Local.RuleOccurs r rules →
  ⊥
equalSinkCannotBeSource r sourceEq occurs
  with occurs
... | Local.ruleHere = contradiction sourceEq
... | Local.ruleThere rest = recurse rest sourceEq
  where
    contradiction : Local.sourceState r ≡ equalState → ⊥
    contradiction ()

    recurse :
      ∀ {x} →
      Local.RuleOccurs x
        (rFFtrue ∷ rFFend ∷
         rSStrue ∷ rSSmark ∷ rSSend ∷
         rFSmark ∷ rFStrue ∷ rFSend ∷
         rRLtrue ∷ rRLend ∷ rRLm1 ∷ rRLm2 ∷ rRLblank ∷
         rCSmark ∷ rCStrue ∷ rCSend ∷ []) →
      Local.sourceState x ≡ equalState → ⊥
    recurse Local.ruleHere ()
    recurse (Local.ruleThere Local.ruleHere) ()
    recurse (Local.ruleThere (Local.ruleThere Local.ruleHere)) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))))))))) ()
    recurse (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))))))))))))))) sourceEq

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- Literal equality microcode and quiescent sinks are now explicit.  The next
-- finite task is the dispatch-uniqueness inversion plus the run theorem
-- relating this mark/shuttle implementation to equality of unary field lengths.
------------------------------------------------------------------------
