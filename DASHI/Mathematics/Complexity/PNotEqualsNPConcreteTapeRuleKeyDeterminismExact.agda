module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact where

------------------------------------------------------------------------
-- RULE-KEY DETERMINISM FOR THE ACTUAL ConcreteTapeMachine RULE LIST
--
-- Operational lookup is first-match.  The raw relational MachineStep may
-- select any listed rule.  The exact compatibility condition is therefore:
-- two listed rules with the same (sourceState, readSymbol) key are equal.
--
-- This owner does not change ConcreteTapeMachine and does not add another
-- transition function.  It proves completeness of the existing sequential
-- scan and uniqueness of its selected rule under that explicit predicate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter

------------------------------------------------------------------------
-- Deterministic rule-table key predicate.
------------------------------------------------------------------------

RuleKeyDeterministic : Local.ConcreteTapeMachine → Set
RuleKeyDeterministic machine =
  ∀ {first second :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)} →
  Local.RuleOccurs first (Local.rules machine) →
  Local.RuleOccurs second (Local.rules machine) →
  Local.sourceState first ≡ Local.sourceState second →
  Local.readSymbol first ≡ Local.readSymbol second →
  first ≡ second

------------------------------------------------------------------------
-- Any listed rule whose key matches (q,a) guarantees that the sequential
-- scan succeeds.  No determinism assumption is needed for existence: the
-- scan may legally stop at an earlier matching rule.
------------------------------------------------------------------------

scanRuleTableComplete :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  (rules :
    List
      (Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine))) →
  (wanted :
    Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) →
  Local.RuleOccurs wanted rules →
  Local.sourceState wanted ≡ q →
  Local.readSymbol wanted ≡ a →
  Σ (Interpreter.MatchedRule machine q a rules)
    (λ matched →
      Interpreter.scanRuleTable machine q a rules ≡ just matched)
scanRuleTableComplete machine q a [] wanted () sourceEq readEq
scanRuleTableComplete machine q a (rule ∷ rest) .rule
    Local.ruleHere sourceEq readEq
    rewrite sourceEq
          | readEq
          | Local.decideEqualRefl (Local.finiteState machine) q
          | Local.decideEqualRefl (Local.finiteSymbol machine) a =
  Interpreter.matched-rule rule Local.ruleHere refl refl , refl
scanRuleTableComplete machine q a (rule ∷ rest) wanted
    (Local.ruleThere occurs) sourceEq readEq
    with
      Local.decideEqual (Local.finiteState machine)
        (Local.sourceState rule) q
       |
      Local.decideEqual (Local.finiteSymbol machine)
        (Local.readSymbol rule) a
... | true | true =
  Interpreter.matched-rule
    rule
    Local.ruleHere
    (Local.decideEqualSound (Local.finiteState machine) refl)
    (Local.decideEqualSound (Local.finiteSymbol machine) refl)
  , refl
... | true | false
    with scanRuleTableComplete machine q a rest wanted occurs sourceEq readEq
...   | matched , scanEq rewrite scanEq =
  Interpreter.liftMatchedRule matched , refl
... | false | true
    with scanRuleTableComplete machine q a rest wanted occurs sourceEq readEq
...   | matched , scanEq rewrite scanEq =
  Interpreter.liftMatchedRule matched , refl
... | false | false
    with scanRuleTableComplete machine q a rest wanted occurs sourceEq readEq
...   | matched , scanEq rewrite scanEq =
  Interpreter.liftMatchedRule matched , refl

fetchConcreteRuleComplete :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  (wanted :
    Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) →
  Local.RuleOccurs wanted (Local.rules machine) →
  Local.sourceState wanted ≡ q →
  Local.readSymbol wanted ≡ a →
  Σ (Interpreter.MatchedRule
      machine q a (Local.rules machine))
    (λ matched →
      Interpreter.fetchConcreteRule machine q a ≡ just matched)
fetchConcreteRuleComplete machine q a wanted occurs sourceEq readEq =
  scanRuleTableComplete
    machine q a (Local.rules machine)
    wanted occurs sourceEq readEq

------------------------------------------------------------------------
-- Under key determinism, every successful first-match result is the unique
-- listed matching rule.
------------------------------------------------------------------------

matchedRuleEqualsAnyMatchingRule :
  ∀ {machine q a wanted}
    (deterministic : RuleKeyDeterministic machine)
    (matched :
      Interpreter.MatchedRule
        machine q a (Local.rules machine)) →
  Local.RuleOccurs wanted (Local.rules machine) →
  Local.sourceState wanted ≡ q →
  Local.readSymbol wanted ≡ a →
  Interpreter.rule matched ≡ wanted
matchedRuleEqualsAnyMatchingRule
    deterministic matched occurs sourceEq readEq =
  deterministic
    (Interpreter.occurs matched)
    occurs
    (trans (Interpreter.sourceExact matched) (sym sourceEq))
    (trans (Interpreter.readExact matched) (sym readEq))

fetchConcreteRuleCompleteUnique :
  ∀ {machine q a wanted}
    (deterministic : RuleKeyDeterministic machine) →
  Local.RuleOccurs wanted (Local.rules machine) →
  Local.sourceState wanted ≡ q →
  Local.readSymbol wanted ≡ a →
  Σ (Interpreter.MatchedRule
      machine q a (Local.rules machine))
    (λ matched →
      Interpreter.fetchConcreteRule machine q a ≡ just matched
      × Interpreter.rule matched ≡ wanted)
fetchConcreteRuleCompleteUnique
    {machine} {q} {a} {wanted}
    deterministic occurs sourceEq readEq
    with fetchConcreteRuleComplete
      machine q a wanted occurs sourceEq readEq
... | matched , scanEq =
  matched ,
    scanEq ,
    matchedRuleEqualsAnyMatchingRule
      deterministic matched occurs sourceEq readEq

------------------------------------------------------------------------
-- Conversely, `nothing` is a genuine absence certificate for that key.
------------------------------------------------------------------------

fetchConcreteRuleNothingNoMatchingRule :
  ∀ {machine q a} →
  Interpreter.fetchConcreteRule machine q a ≡ nothing →
  (wanted :
    Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) →
  Local.RuleOccurs wanted (Local.rules machine) →
  Local.sourceState wanted ≡ q →
  Local.readSymbol wanted ≡ a →
  ⊥
fetchConcreteRuleNothingNoMatchingRule
    {machine} {q} {a} fetchNone
    wanted occurs sourceEq readEq
    with fetchConcreteRuleComplete
      machine q a wanted occurs sourceEq readEq
... | matched , scanEq
    with trans (sym scanEq) fetchNone
... | ()

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
-- * explicit deterministic-key predicate on the literal existing rule list;
-- * sequential first-match lookup is complete for every listed matching key;
-- * under key determinism, the returned rule equals any relationally chosen
--   listed rule with that key;
-- * `nothing` proves there is no listed rule with the queried key.
--
-- NEXT:
-- * consume `fetchConcreteRuleCompleteUnique` in the intrinsic row executor
--   and prove executable output equals every relational WellFormedMachineStep
--   on deterministic-key machines;
-- * then leave interpreter engineering and pay standard-TM polynomial
--   simulation/clock transport.
------------------------------------------------------------------------
