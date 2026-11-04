module DASHI.Mathematics.Complexity.CodedFiniteStandardSingletonLinkExact where

------------------------------------------------------------------------
-- ONE FRESH DISPATCH KEY -> ONE SAFE CROSS-MODE LINK
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link

ResidentKeyFresh :
  ∀ {symbols : Nat}
    (fragment : Mode.CodedModeFragment symbols) →
  Fin.Fin (Mode.stateCount fragment) →
  Fin.Fin symbols → Set
ResidentKeyFresh fragment source read =
  ∀ {resident} →
  Local.RuleOccurs resident (Mode.rules fragment) →
  Local.sourceState resident ≡ source →
  Local.readSymbol resident ≡ read →
  ⊥

singletonRuleUnique :
  ∀ {State Symbol : Set}
    (rule : Local.TapeRule State Symbol) →
  Link.RuleTableUnique (rule ∷ [])
singletonRuleUnique rule Local.ruleHere Local.ruleHere sourceEq readEq = refl
singletonRuleUnique rule Local.ruleHere (Local.ruleThere ()) sourceEq readEq
singletonRuleUnique rule (Local.ruleThere ()) second sourceEq readEq

residentSingletonDisjoint :
  ∀ {symbols : Nat}
    {fragment : Mode.CodedModeFragment symbols}
    {source target : Fin.Fin (Mode.stateCount fragment)}
    {read write : Fin.Fin symbols}
    {direction : Local.Direction} →
  ResidentKeyFresh fragment source read →
  Link.RuleKeyDisjoint
    (Mode.rules fragment)
    (Local.tape-rule source read target write direction ∷ [])
residentSingletonDisjoint fresh residentOccurs Local.ruleHere sourceEq readEq =
  fresh residentOccurs sourceEq readEq
residentSingletonDisjoint fresh residentOccurs (Local.ruleThere ()) sourceEq readEq

singletonSafeLinkExtension :
  ∀ {symbols : Nat}
    {fragment : Mode.CodedModeFragment symbols}
    {source target : Fin.Fin (Mode.stateCount fragment)}
    {read write : Fin.Fin symbols}
    {direction : Local.Direction} →
  ResidentKeyFresh fragment source read →
  Link.SafeLinkExtension fragment
singletonSafeLinkExtension
    {source = source} {target = target}
    {read = read} {write = write} {direction = direction}
    fresh = record
  { Link.links =
      Local.tape-rule source read target write direction ∷ []
  ; Link.linksUnique =
      singletonRuleUnique
        (Local.tape-rule source read target write direction)
  ; Link.residentLinkKeyDisjoint =
      residentSingletonDisjoint fresh
  }

extendWithFreshSingleton :
  ∀ {symbols : Nat}
    {fragment : Mode.CodedModeFragment symbols}
    {source target : Fin.Fin (Mode.stateCount fragment)}
    {read write : Fin.Fin symbols}
    {direction : Local.Direction} →
  ResidentKeyFresh fragment source read →
  Mode.CodedModeFragment symbols
extendWithFreshSingleton fresh =
  Link.extendFragmentWithLinks
    (singletonSafeLinkExtension fresh)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Each generator-call, generator-return or final-negation bridge can now be
-- added by proving exactly one local fact: the resident machine has no existing
-- rule for that source/read key.  Determinism of the singleton link and of the
-- combined table is then constructed automatically.
------------------------------------------------------------------------
