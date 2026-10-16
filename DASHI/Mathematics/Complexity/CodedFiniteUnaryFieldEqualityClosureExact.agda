module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureExact where

------------------------------------------------------------------------
-- CLOSE THE UNARY-FIELD EQUALITY MICROCODE INTO AN ACTUAL CODED STANDARD TM
--
-- The microcode owner deliberately stopped before manufacturing dispatch
-- uniqueness.  This tranche pays exactly that finite syntactic obligation.
-- Rather than enumerate all 17 x 17 rule pairs, each listed rule is recovered
-- from its numeric dispatch key `state * symbolCount + symbol`; equality of
-- source/read keys therefore forces equality of the literal listed rules.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityExact as Equality

Rule : Set
Rule =
  Local.TapeRule
    (Fin.Fin Equality.stateCount)
    (Fin.Fin Equality.symbolCount)

------------------------------------------------------------------------
-- 1. A finite inverse table for the literal dispatch keys.
------------------------------------------------------------------------

keyLookup : Nat → Maybe Rule
keyLookup zero = nothing
keyLookup (suc zero) = just Equality.rFFtrue
keyLookup (suc (suc zero)) = just Equality.rFFend
keyLookup (suc (suc (suc zero))) = just Equality.rFFmark
keyLookup (suc (suc (suc (suc zero)))) = nothing
keyLookup (suc (suc (suc (suc (suc zero))))) = nothing
keyLookup (suc (suc (suc (suc (suc (suc zero)))))) = just Equality.rSStrue
keyLookup (suc (suc (suc (suc (suc (suc (suc zero))))))) = just Equality.rSSend
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = just Equality.rSSmark
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = nothing
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = nothing
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = just Equality.rFStrue
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = just Equality.rFSend
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = nothing
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = just Equality.rFSmark
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = just Equality.rRLblank
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))) = just Equality.rRLtrue
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))) = just Equality.rRLend
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))) = just Equality.rRLm1
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))) = just Equality.rRLm2
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))) = nothing
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) = just Equality.rCStrue
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) = just Equality.rCSend
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) = nothing
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) = just Equality.rCSmark
keyLookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) = nothing

------------------------------------------------------------------------
-- 2. Every literal listed rule is recovered by its key.
------------------------------------------------------------------------

listedRuleDecoded :
  ∀ {rule : Rule} →
  Local.RuleOccurs rule Equality.rules →
  keyLookup (Equality.keyCode rule) ≡ just rule
listedRuleDecoded Local.ruleHere = refl
listedRuleDecoded (Local.ruleThere Local.ruleHere) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere Local.ruleHere)) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere))))))))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere Local.ruleHere)))))))))))))))) = refl
listedRuleDecoded (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))))))))))))))))

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

sameDispatchKeyCode :
  (left right : Rule) →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  Equality.keyCode left ≡ Equality.keyCode right
sameDispatchKeyCode left right refl refl = refl

fieldEqualityKeyUnique :
  ∀ {left right : Rule} →
  Local.RuleOccurs left Equality.rules →
  Local.RuleOccurs right Equality.rules →
  Equality.keyCode left ≡ Equality.keyCode right →
  left ≡ right
fieldEqualityKeyUnique leftOccurs rightOccurs keyEq =
  justInjective
    (trans
      (sym (listedRuleDecoded leftOccurs))
      (trans
        (cong keyLookup keyEq)
        (listedRuleDecoded rightOccurs)))
  where
    open import Relation.Binary.PropositionalEquality using (trans; sym)

fieldEqualityDispatchUnique :
  ∀ {left right : Rule} →
  Local.RuleOccurs left Equality.rules →
  Local.RuleOccurs right Equality.rules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
fieldEqualityDispatchUnique leftOccurs rightOccurs sourceEq readEq =
  fieldEqualityKeyUnique
    leftOccurs rightOccurs
    (sameDispatchKeyCode _ _ sourceEq readEq)

------------------------------------------------------------------------
-- 3. Actual coded standard machine closure.
------------------------------------------------------------------------

fieldEqualityCode : Coded.CodedFiniteStandardTM
fieldEqualityCode = record
  { Coded.stateCount = Equality.stateCount
  ; Coded.symbolCount = Equality.symbolCount
  ; Coded.blank = Equality.blank
  ; Coded.initialState = Equality.findFirst
  ; Coded.acceptingState = Equality.equalState
  ; Coded.rules = Equality.rules
  ; Coded.dispatchUnique = fieldEqualityDispatchUnique
  }

fieldEqualityMachine :
  Standard.StandardSingleTapeMachine
    (Fin.Fin Equality.stateCount)
    (Fin.Fin Equality.symbolCount)
fieldEqualityMachine =
  Presented.finitePresentedStandardMachine
    (Coded.decodeCodedStandardTM fieldEqualityCode)

------------------------------------------------------------------------
-- 4. Both result sinks are quiescent in the closed machine.
------------------------------------------------------------------------

equalSinkQuiescent :
  (symbol : Fin.Fin Equality.symbolCount) →
  Standard.transition fieldEqualityMachine Equality.equalState symbol ≡ nothing
equalSinkQuiescent Fin.zero = refl
equalSinkQuiescent (Fin.suc Fin.zero) = refl
equalSinkQuiescent (Fin.suc (Fin.suc Fin.zero)) = refl
equalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl
equalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = refl

unequalSinkQuiescent :
  (symbol : Fin.Fin Equality.symbolCount) →
  Standard.transition fieldEqualityMachine Equality.unequalState symbol ≡ nothing
unequalSinkQuiescent Fin.zero = refl
unequalSinkQuiescent (Fin.suc Fin.zero) = refl
unequalSinkQuiescent (Fin.suc (Fin.suc Fin.zero)) = refl
unequalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl
unequalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Unary field equality is now literal deterministic coded-standard syntax with
-- quiescent equal/unequal sinks.  The remaining microcode payment is run-level
-- correctness: the mark/shuttle machine reaches `equalState` iff the two unary
-- payload lengths agree, with its exact work bound.
------------------------------------------------------------------------
