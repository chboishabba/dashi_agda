module DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableGeneratorExact where

------------------------------------------------------------------------
-- ONE FIXED GUARDED COOK FORMULA -> LITERAL FINITE BIT-TABLE GENERATOR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact as Cursor
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact as Lookup
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupTransitionExact as LookupTransition
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Canonical
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

cookBits : Description.GuardedCookFormulaDescription → List Bool
cookBits description =
  Binary.encodeFormulaBits (Description.formula description)

cookBitCount : Description.GuardedCookFormulaDescription → Nat
cookBitCount description = Binary.listLength (cookBits description)

listFinBit :
  (bits : List Bool) → Fin.Fin (Binary.listLength bits) → Bool
listFinBit [] ()
listFinBit (bit ∷ rest) Fin.zero = bit
listFinBit (bit ∷ rest) (Fin.suc index) = listFinBit rest index

listFinBitLookupExact :
  (bits : List Bool) →
  (index : Fin.Fin (Binary.listLength bits)) →
  Canonical.lookupBit (Fin.toℕ index) bits ≡ just (listFinBit bits index)
listFinBitLookupExact [] ()
listFinBitLookupExact (bit ∷ rest) Fin.zero = refl
listFinBitLookupExact (bit ∷ rest) (Fin.suc index) =
  listFinBitLookupExact rest index

cookBitAt :
  (description : Description.GuardedCookFormulaDescription) →
  Fin.Fin (cookBitCount description) → Bool
cookBitAt description = listFinBit (cookBits description)

cookBitAtQueryAnswerExact :
  (description : Description.GuardedCookFormulaDescription) →
  (index : Fin.Fin (cookBitCount description)) →
  Semantics.queryAnswer
    (Description.atIndex description (Fin.toℕ index))
  ≡ just (cookBitAt description index)
cookBitAtQueryAnswerExact description index =
  listFinBitLookupExact (cookBits description) index

fixedCookLookupCode :
  (description : Description.GuardedCookFormulaDescription) →
  Coded.CodedFiniteStandardTM
fixedCookLookupCode description =
  Lookup.lookupCode
    (cookBitCount description)
    (cookBitAt description)

fixedCookValidStopTransition :
  (description : Description.GuardedCookFormulaDescription) →
  (index : Fin.Fin (cookBitCount description)) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (fixedCookLookupCode description)))
    (Lookup.cursorInBase
      (cookBitCount description)
      (Phase.raisePhase index))
    Cursor.stopSymbol
  ≡
  just
    (Standard.standard-transition
      (Lookup.bitSink
        (cookBitCount description)
        (cookBitAt description index))
      Cursor.stopSymbol
      Local.stayPut)
fixedCookValidStopTransition description index =
  LookupTransition.validStopTransition (cookBitAt description) index

------------------------------------------------------------------------
-- SAME-OBJECT FIREWALL
------------------------------------------------------------------------

record FixedTableGeneratorBoundary
    (description : Description.GuardedCookFormulaDescription) : Set₁ where
  field
    generatedCode : Coded.CodedFiniteStandardTM
    generatedCodeExact : generatedCode ≡ fixedCookLookupCode description
    sameObjectCode : generatedCode ≡ Description.code description

open FixedTableGeneratorBoundary public

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- For every already-fixed description, all in-range Cook bits are compiled into
-- ordinary finite standard-TM syntax.  Self-reference still requires literal
-- same-object code identity; the companion no-go proves table baking cannot pay
-- that identity under the repository's one-hot state codec.
------------------------------------------------------------------------
