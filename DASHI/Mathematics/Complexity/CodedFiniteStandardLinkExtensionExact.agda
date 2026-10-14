module DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact where

------------------------------------------------------------------------
-- SAFE CROSS-MODE LINK RULES FOR ONE CODED FINITE STANDARD MACHINE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ left) right = x ∷ append left right

data AppendOccurrence {State Symbol : Set}
    (rule : Local.TapeRule State Symbol)
    (left right : List (Local.TapeRule State Symbol)) : Set where
  occursLeft :
    Local.RuleOccurs rule left → AppendOccurrence rule left right
  occursRight :
    Local.RuleOccurs rule right → AppendOccurrence rule left right

splitAppendOccurrence :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    (left right : List (Local.TapeRule State Symbol)) →
  Local.RuleOccurs rule (append left right) →
  AppendOccurrence rule left right
splitAppendOccurrence [] right occurs = occursRight occurs
splitAppendOccurrence (x ∷ left) right Local.ruleHere =
  occursLeft Local.ruleHere
splitAppendOccurrence (x ∷ left) right (Local.ruleThere occurs)
  with splitAppendOccurrence left right occurs
... | occursLeft leftOccurs = occursLeft (Local.ruleThere leftOccurs)
... | occursRight rightOccurs = occursRight rightOccurs

RuleTableUnique :
  ∀ {State Symbol : Set} →
  List (Local.TapeRule State Symbol) → Set
RuleTableUnique rules =
  ∀ {left right} →
  Local.RuleOccurs left rules →
  Local.RuleOccurs right rules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right

RuleKeyDisjoint :
  ∀ {State Symbol : Set} →
  List (Local.TapeRule State Symbol) →
  List (Local.TapeRule State Symbol) → Set
RuleKeyDisjoint leftRules rightRules =
  ∀ {left right} →
  Local.RuleOccurs left leftRules →
  Local.RuleOccurs right rightRules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  ⊥

appendDispatchUnique :
  ∀ {State Symbol : Set}
    (left right : List (Local.TapeRule State Symbol)) →
  RuleTableUnique left →
  RuleTableUnique right →
  RuleKeyDisjoint left right →
  RuleTableUnique (append left right)
appendDispatchUnique left right leftUnique rightUnique disjoint
    firstOccurs secondOccurs sourceEq readEq
  with splitAppendOccurrence left right firstOccurs
     | splitAppendOccurrence left right secondOccurs
... | occursLeft firstLeft | occursLeft secondLeft =
  leftUnique firstLeft secondLeft sourceEq readEq
... | occursRight firstRight | occursRight secondRight =
  rightUnique firstRight secondRight sourceEq readEq
... | occursLeft firstLeft | occursRight secondRight =
  ⊥-elim (disjoint firstLeft secondRight sourceEq readEq)
... | occursRight firstRight | occursLeft secondLeft =
  ⊥-elim (disjoint secondLeft firstRight (sym sourceEq) (sym readEq))
  where
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

record SafeLinkExtension {symbols : Nat}
    (fragment : Mode.CodedModeFragment symbols) : Set where
  field
    links :
      List
        (Local.TapeRule
          (Fin.Fin (Mode.stateCount fragment))
          (Fin.Fin symbols))

    linksUnique : RuleTableUnique links

    residentLinkKeyDisjoint :
      RuleKeyDisjoint (Mode.rules fragment) links

open SafeLinkExtension public

extendFragmentWithLinks :
  ∀ {symbols}
    {fragment : Mode.CodedModeFragment symbols} →
  SafeLinkExtension fragment →
  Mode.CodedModeFragment symbols
extendFragmentWithLinks {fragment = fragment} extension = record
  { Mode.stateCount = Mode.stateCount fragment
  ; Mode.rules = append (Mode.rules fragment) (links extension)
  ; Mode.dispatchUnique =
      appendDispatchUnique
        (Mode.rules fragment)
        (links extension)
        (Mode.dispatchUnique fragment)
        (linksUnique extension)
        (residentLinkKeyDisjoint extension)
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- A compiler may now proceed in two literal stages:
--   1. disjoint-sum independently deterministic finite mode fragments;
--   2. append explicit cross-mode call/return/suffix rules, accompanied by a
--      proof that their dispatch keys are fresh relative to resident rules.
--
-- This is actual CodedFiniteStandardTM rule-table construction plumbing.  It
-- does not assume an extensional interpreter or arbitrary transition oracle.
------------------------------------------------------------------------
