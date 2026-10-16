module DASHI.Mathematics.Complexity.PNotEqualsNPCodedQuoteGuardedOwnCookKleeneExact where

------------------------------------------------------------------------
-- QUOTE-GUARDED BEHAVIOURAL FIXED POINT FOR ONE OWN-COOK DESCRIPTION
--
-- A fixed description D supplies the candidate machine/input/T.  The binary
-- primitive does not blindly use D: it first inspects the quoted finite Kleene
-- syntax, recovers its primitive coded machine, and compares the literal static
-- program bits with D's actual machine quotation.  Only a matching quotation is
-- allowed to answer the requested streamed Cook bit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuotationExact as Quote
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedQuoteSensitiveKleeneExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedPointOwnCookStreamingExact as OwnStream

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

andBool : Bool → Bool → Bool
andBool false right = false
andBool true right = right

sameBoolList : List Bool → List Bool → Bool
sameBoolList [] [] = true
sameBoolList [] (_ ∷ _) = false
sameBoolList (_ ∷ _) [] = false
sameBoolList (left ∷ ls) (right ∷ rs) =
  andBool (boolEqual left right) (sameBoolList ls rs)

sameBoolListRefl :
  (bits : List Bool) →
  sameBoolList bits bits ≡ true
sameBoolListRefl [] = refl
sameBoolListRefl (false ∷ rest)
  rewrite sameBoolListRefl rest = refl
sameBoolListRefl (true ∷ rest)
  rewrite sameBoolListRefl rest = refl

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

quoteMatchesDescription :
  (description : Description.GuardedCookFormulaDescription) →
  Code.Program DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.CodedFiniteStandardTM →
  Bool
quoteMatchesDescription description quoted =
  sameBoolList
    (Quote.codedStaticProgramList (Kleene.headMachine quoted))
    (Quote.codedStaticProgramList (Description.code description))

selectQuotedCookBit :
  Bool → Maybe Bool → Maybe Bool
selectQuotedCookBit false answer = nothing
selectQuotedCookBit true answer = answer

guardedOwnCookSemantics :
  (description : Description.GuardedCookFormulaDescription) →
  Code.PrimitiveSemantics
    DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.CodedFiniteStandardTM
    Nat
    Bool
guardedOwnCookSemantics description = record
  { Code.runPrimitive1 = λ machine index → nothing
  ; Code.runPrimitive2 = λ machine quoted index →
      selectQuotedCookBit
        (quoteMatchesDescription description quoted)
        (OwnStream.recoveredOwnCookBit description index)
  }

guardedOwnCookFixedPoint :
  (description : Description.GuardedCookFormulaDescription) →
  Code.Program DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.CodedFiniteStandardTM
guardedOwnCookFixedPoint description =
  Code.primitiveBodyFixedPoint (Description.code description)

fixedPointQuoteGuardTrue :
  (description : Description.GuardedCookFormulaDescription) →
  quoteMatchesDescription
    description
    (guardedOwnCookFixedPoint description)
  ≡ true
fixedPointQuoteGuardTrue description =
  sameBoolListRefl
    (Quote.codedStaticProgramList (Description.code description))

guardedOwnCookFixedPointRunExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Code.run1
    (guardedOwnCookSemantics description)
    (guardedOwnCookFixedPoint description)
    index
  ≡ OwnStream.recoveredOwnCookBit description index
guardedOwnCookFixedPointRunExact description index
  rewrite fixedPointQuoteGuardTrue description = refl

guardedOwnCookFixedPointSemanticExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Code.run1
    (guardedOwnCookSemantics description)
    (guardedOwnCookFixedPoint description)
    index
  ≡ Semantics.queryAnswer (Description.atIndex description index)
guardedOwnCookFixedPointSemanticExact description index =
  trans
    (guardedOwnCookFixedPointRunExact description index)
    (OwnStream.recoveredOwnCookBitExact description index)

------------------------------------------------------------------------
-- Semantic work envelope: the static quotation guard is a description constant;
-- the varying indexed Cook work keeps the already-proved linear bound.
------------------------------------------------------------------------

quoteGuardWork :
  Description.GuardedCookFormulaDescription → Nat
quoteGuardWork description =
  listLength (Quote.codedStaticProgramList (Description.code description))

guardedSemanticWork :
  Description.GuardedCookFormulaDescription → Nat → Nat
guardedSemanticWork description index =
  quoteGuardWork description
  + OwnStream.recoveredOwnCookWork description index

guardedSemanticWorkBound :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  guardedSemanticWork description index
  ≤
  quoteGuardWork description
  + Cost.fixedDescriptionIndexBudget
      (DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedPointOwnCookDescriptionExact.fixedPointRecoveredDescription description)
      index
guardedSemanticWorkBound description index =
  NatP.+-monoʳ-≤
    (quoteGuardWork description)
    (OwnStream.recoveredOwnCookWorkByIndex description index)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The surviving self-reference route now has an actual quote-dependent finite
-- Kleene body: changing the quoted static program bits can suppress execution,
-- while its constructed fixed point passes the quotation guard and returns the
-- canonical streamed bit of its own guarded Cook formula.
--
-- This is still semantic execution in Agda. The next and now singular compiler
-- obligation is to realize this guard + streamed recursion as literal
-- `CodedFiniteStandardTM` execution with a proved resource coefficient.
------------------------------------------------------------------------
