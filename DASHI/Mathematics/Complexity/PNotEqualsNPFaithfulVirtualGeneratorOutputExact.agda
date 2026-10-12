module DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualGeneratorOutputExact where

------------------------------------------------------------------------
-- MACHINE-STATE OUTPUT RECEIPT FOR THE UNIVERSAL GUARDED-COOK BIT GENERATOR
--
-- An arbitrary meta-level `outputBit : Configuration -> Maybe Bool` is too weak
-- for resource-critical use: it could inspect an entire final configuration for
-- free.  This owner requires the computed answer to live in the target machine's
-- own finite control state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as VirtualFrontier
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

record FaithfulGeneratorOutput
    {presentation : Presented.FinitePresentedStandardTM}
    (generator :
      VirtualFrontier.UniversalGuardedCookBitGenerator presentation) : Set₁ where
  field
    noneState : Presented.State presentation
    falseState : Presented.State presentation
    trueState : Presented.State presentation

    noneNotFalse : noneState ≡ falseState → ⊥
    noneNotTrue : noneState ≡ trueState → ⊥
    falseNotTrue : falseState ≡ trueState → ⊥

    finishStateExact :
      (query : Query.GuardedCookBitQuery) →
      Standard.state
        (VirtualFrontier.finishConfiguration generator query)
      ≡ outputState (Semantics.queryAnswer query)
  where
    outputState : Maybe Bool → Presented.State presentation
    outputState nothing = noneState
    outputState (just false) = falseState
    outputState (just true) = trueState

open FaithfulGeneratorOutput public

outputState :
  ∀ {presentation generator} →
  FaithfulGeneratorOutput
    {presentation = presentation} generator →
  Maybe Bool → Presented.State presentation
outputState faithful nothing = noneState faithful
outputState faithful (just false) = falseState faithful
outputState faithful (just true) = trueState faithful

outputStateInjective :
  ∀ {presentation generator}
    (faithful : FaithfulGeneratorOutput
      {presentation = presentation} generator)
    {left right : Maybe Bool} →
  outputState faithful left ≡ outputState faithful right →
  left ≡ right
outputStateInjective faithful {nothing} {nothing} proof = refl
outputStateInjective faithful {nothing} {just false} proof =
  ⊥-elim (noneNotFalse faithful proof)
  where
    ⊥-elim : ⊥ → nothing ≡ just false
    ⊥-elim ()
outputStateInjective faithful {nothing} {just true} proof =
  ⊥-elim (noneNotTrue faithful proof)
  where
    ⊥-elim : ⊥ → nothing ≡ just true
    ⊥-elim ()
outputStateInjective faithful {just false} {nothing} proof =
  ⊥-elim (noneNotFalse faithful (sym proof))
  where
    ⊥-elim : ⊥ → just false ≡ nothing
    ⊥-elim ()
outputStateInjective faithful {just true} {nothing} proof =
  ⊥-elim (noneNotTrue faithful (sym proof))
  where
    ⊥-elim : ⊥ → just true ≡ nothing
    ⊥-elim ()
outputStateInjective faithful {just false} {just false} proof = refl
outputStateInjective faithful {just true} {just true} proof = refl
outputStateInjective faithful {just false} {just true} proof =
  ⊥-elim (falseNotTrue faithful proof)
  where
    ⊥-elim : ⊥ → just false ≡ just true
    ⊥-elim ()
outputStateInjective faithful {just true} {just false} proof =
  ⊥-elim (falseNotTrue faithful (sym proof))
  where
    ⊥-elim : ⊥ → just true ≡ just false
    ⊥-elim ()

------------------------------------------------------------------------
-- A successful output is now witnessed by the ACTUAL machine state tag.
------------------------------------------------------------------------

record FaithfulSuccessfulQuery
    {presentation : Presented.FinitePresentedStandardTM}
    (generator : VirtualFrontier.UniversalGuardedCookBitGenerator presentation)
    (faithful : FaithfulGeneratorOutput generator)
    (query : Query.GuardedCookBitQuery)
    (bit : Bool) : Set where
  field
    finalStateIsBit :
      Standard.state
        (VirtualFrontier.finishConfiguration generator query)
      ≡ outputState faithful (just bit)

open FaithfulSuccessfulQuery public

faithfulSuccessfulQueryAnswerExact :
  ∀ {presentation generator}
    {faithful : FaithfulGeneratorOutput
      {presentation = presentation} generator}
    {query bit} →
  FaithfulSuccessfulQuery generator faithful query bit →
  Semantics.queryAnswer query ≡ just bit
faithfulSuccessfulQueryAnswerExact
    {generator = generator} {faithful = faithful} {query = query}
    successful =
  outputStateInjective faithful
    (trans
      (sym (finishStateExact faithful query))
      (finalStateIsBit successful))

faithfulSuccessfulQuerySound :
  ∀ {presentation generator}
    {faithful : FaithfulGeneratorOutput
      {presentation = presentation} generator}
    {query bit} →
  FaithfulSuccessfulQuery generator faithful query bit →
  Virtual.BitAt
    (Query.index query)
    (Binary.encodeFormulaBits (Query.queryFormula query))
    bit
faithfulSuccessfulQuerySound successful =
  Semantics.queryAnswerSound
    (faithfulSuccessfulQueryAnswerExact successful)

------------------------------------------------------------------------
-- RESOURCE CONSEQUENCE
--
-- Downstream executable compilation should require FaithfulGeneratorOutput and
-- FaithfulSuccessfulQuery.  The answer is then present in finite machine state;
-- no unrestricted observer of a whole configuration is needed to obtain it.
------------------------------------------------------------------------
