module DASHI.Mathematics.Complexity.CodedFiniteStandardLinkTransitionPreservationExact where

------------------------------------------------------------------------
-- SAFE LINKS DO NOT OVERRIDE RESIDENT STANDARD TRANSITIONS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

residentOccursAfterLink :
  ∀ {symbols : Nat}
    {fragment : Mode.CodedModeFragment symbols}
    (extension : Link.SafeLinkExtension fragment)
    {rule : Local.TapeRule
      (Fin.Fin (Mode.stateCount fragment))
      (Fin.Fin symbols)} →
  Local.RuleOccurs rule (Mode.rules fragment) →
  Local.RuleOccurs rule
    (Mode.rules (Link.extendFragmentWithLinks extension))
residentOccursAfterLink extension Local.ruleHere = Local.ruleHere
residentOccursAfterLink extension (Local.ruleThere occurs) =
  Local.ruleThere (residentOccursAfterLink extension occurs)

closedExtendedCode :
  ∀ {symbols : Nat}
    {fragment : Mode.CodedModeFragment symbols} →
  (extension : Link.SafeLinkExtension fragment) →
  (blank : Fin.Fin symbols) →
  (initial accepting : Fin.Fin (Mode.stateCount fragment)) →
  Coded.CodedFiniteStandardTM
closedExtendedCode {fragment = fragment}
    extension blank initial accepting =
  Mode.closeFragment
    (Link.extendFragmentWithLinks extension)
    blank initial accepting

residentRuleDeterminesExtendedTransition :
  ∀ {symbols : Nat}
    {fragment : Mode.CodedModeFragment symbols}
    (extension : Link.SafeLinkExtension fragment)
    (blank : Fin.Fin symbols)
    (initial accepting : Fin.Fin (Mode.stateCount fragment))
    {rule : Local.TapeRule
      (Fin.Fin (Mode.stateCount fragment))
      (Fin.Fin symbols)} →
  Local.RuleOccurs rule (Mode.rules fragment) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM
        (closedExtendedCode extension blank initial accepting)))
    (Local.sourceState rule)
    (Local.readSymbol rule)
  ≡
  just
    (Standard.standard-transition
      (Local.targetState rule)
      (Local.writeSymbol rule)
      (Local.direction rule))
residentRuleDeterminesExtendedTransition
    extension blank initial accepting occurs
  with Standard.listedRuleDeterminesStandardTransition
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Coded.decodeCodedStandardTM
        (closedExtendedCode extension blank initial accepting)))
    (residentOccursAfterLink extension occurs)
    refl refl
... | matched , fetchExact , transitionExact = transitionExact

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Safe link extension is conservative on every resident dispatch key.  Thus a
-- candidate fragment embedded into a disjoint mode sum remains an exact control
-- submachine after generator-call / return / opposite-suffix links are added,
-- provided those links satisfy the proved key-freshness condition.
------------------------------------------------------------------------
