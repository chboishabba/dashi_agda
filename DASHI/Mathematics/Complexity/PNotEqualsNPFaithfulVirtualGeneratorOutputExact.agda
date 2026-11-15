module DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualGeneratorOutputExact where

------------------------------------------------------------------------
-- MACHINE-STATE OUTPUT RECEIPT FOR THE UNIVERSAL GUARDED-COOK BIT GENERATOR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as VirtualFrontier
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

maybeOutputState :
  ∀ {State : Set} →
  State → State → State → Maybe Bool → State
maybeOutputState none falseState trueState nothing = none
maybeOutputState none falseState trueState (just false) = falseState
maybeOutputState none falseState trueState (just true) = trueState

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
      ≡
      maybeOutputState noneState falseState trueState
        (Semantics.queryAnswer query)

open FaithfulGeneratorOutput public

outputState :
  ∀ {presentation generator} →
  FaithfulGeneratorOutput
    {presentation = presentation} generator →
  Maybe Bool → Presented.State presentation
outputState faithful =
  maybeOutputState
    (noneState faithful)
    (falseState faithful)
    (trueState faithful)

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
outputStateInjective faithful {nothing} {just true} proof =
  ⊥-elim (noneNotTrue faithful proof)
outputStateInjective faithful {just false} {nothing} proof =
  ⊥-elim (noneNotFalse faithful (sym proof))
outputStateInjective faithful {just true} {nothing} proof =
  ⊥-elim (noneNotTrue faithful (sym proof))
outputStateInjective faithful {just false} {just false} proof = refl
outputStateInjective faithful {just true} {just true} proof = refl
outputStateInjective faithful {just false} {just true} proof =
  ⊥-elim (falseNotTrue faithful proof)
outputStateInjective faithful {just true} {just false} proof =
  ⊥-elim (falseNotTrue faithful (sym proof))

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
    {faithful = faithful} {query = query} successful =
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
-- Downstream resource-critical compilation should consume this receipt rather
-- than the weaker extensional output observer in the scaffold generator record.
------------------------------------------------------------------------
