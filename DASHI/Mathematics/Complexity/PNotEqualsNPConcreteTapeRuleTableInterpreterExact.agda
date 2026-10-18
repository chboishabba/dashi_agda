module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact where

------------------------------------------------------------------------
-- OPERATIONAL INTERPRETER FOR THE EXISTING ConcreteTapeMachine RULE TABLE
--
-- This owner does NOT introduce a new machine language. It consumes the
-- literal finite rule list already carried by ConcreteTapeMachine.
--
-- Given a current state q and scanned symbol a, it sequentially searches
-- the machine's own rule table. A successful result carries:
--   * the exact returned rule;
--   * a proof that this rule occurs in the machine table;
--   * equality of its source state with q;
--   * equality of its read symbol with a.
--
-- Work is the number of table entries inspected, and is bounded by the
-- literal rule-table length. Thus one operational rule fetch cannot hide
-- an extensional transition oracle.
--
-- This is a key adapter toward machine-model invariance, but it is not yet
-- a whole-tape step/run simulator or a theorem equating DASHI's model with
-- every standard deterministic Turing-machine presentation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical

------------------------------------------------------------------------
-- A returned rule is theorem-bearing evidence about the ACTUAL table.
------------------------------------------------------------------------

record MatchedRule
    (machine : Local.ConcreteTapeMachine)
    (q : Local.State machine)
    (a : Local.Symbol machine)
    (rules :
      List
        (Local.TapeRule
          (Local.State machine)
          (Local.Symbol machine))) : Set where
  constructor matched-rule
  field
    rule :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)
    occurs :
      Local.RuleOccurs rule rules
    sourceExact :
      Local.sourceState rule ≡ q
    readExact :
      Local.readSymbol rule ≡ a

open MatchedRule public

liftMatchedRule :
  ∀ {machine q a}
    {head :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)}
    {tail} →
  MatchedRule machine q a tail →
  MatchedRule machine q a (head ∷ tail)
liftMatchedRule (matched-rule rule occurrence sourceEq readEq) =
  matched-rule
    rule
    (Local.ruleThere occurrence)
    sourceEq
    readEq

------------------------------------------------------------------------
-- Literal sequential scan using the finite enumeration equality deciders.
------------------------------------------------------------------------

scanRuleTable :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  (rules :
    List
      (Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine))) →
  Maybe (MatchedRule machine q a rules)
scanRuleTable machine q a [] =
  nothing
scanRuleTable machine q a (rule ∷ rest)
    with
      Local.decideEqual (Local.finiteState machine)
        (Local.sourceState rule) q
       |
      Local.decideEqual (Local.finiteSymbol machine)
        (Local.readSymbol rule) a
... | true | true =
  just
    (matched-rule
      rule
      Local.ruleHere
      (Local.decideEqualSound
        (Local.finiteState machine) refl)
      (Local.decideEqualSound
        (Local.finiteSymbol machine) refl))
... | true | false
    with scanRuleTable machine q a rest
...   | nothing = nothing
...   | just matched = just (liftMatchedRule matched)
... | false | true
    with scanRuleTable machine q a rest
...   | nothing = nothing
...   | just matched = just (liftMatchedRule matched)
... | false | false
    with scanRuleTable machine q a rest
...   | nothing = nothing
...   | just matched = just (liftMatchedRule matched)

------------------------------------------------------------------------
-- Work counter: exactly one table-entry inspection per recursive layer.
------------------------------------------------------------------------

scanRuleWork :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  (rules :
    List
      (Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine))) →
  Nat
scanRuleWork machine q a [] =
  zero
scanRuleWork machine q a (rule ∷ rest)
    with
      Local.decideEqual (Local.finiteState machine)
        (Local.sourceState rule) q
       |
      Local.decideEqual (Local.finiteSymbol machine)
        (Local.readSymbol rule) a
... | true | true = suc zero
... | true | false =
  suc (scanRuleWork machine q a rest)
... | false | true =
  suc (scanRuleWork machine q a rest)
... | false | false =
  suc (scanRuleWork machine q a rest)

scanRuleWorkBound :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  (rules :
    List
      (Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine))) →
  scanRuleWork machine q a rules
  ≤ Canonical.listLength rules
scanRuleWorkBound machine q a [] =
  z≤n
scanRuleWorkBound machine q a (rule ∷ rest)
    with
      Local.decideEqual (Local.finiteState machine)
        (Local.sourceState rule) q
       |
      Local.decideEqual (Local.finiteSymbol machine)
        (Local.readSymbol rule) a
... | true | true =
  s≤s z≤n
... | true | false =
  s≤s (scanRuleWorkBound machine q a rest)
... | false | true =
  s≤s (scanRuleWorkBound machine q a rest)
... | false | false =
  s≤s (scanRuleWorkBound machine q a rest)

------------------------------------------------------------------------
-- Specialize to the ACTUAL machine rule list.
------------------------------------------------------------------------

fetchConcreteRule :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  Maybe
    (MatchedRule
      machine q a
      (Local.rules machine))
fetchConcreteRule machine q a =
  scanRuleTable machine q a (Local.rules machine)

fetchConcreteRuleWork :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  Nat
fetchConcreteRuleWork machine q a =
  scanRuleWork machine q a (Local.rules machine)

fetchConcreteRuleWorkBound :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  fetchConcreteRuleWork machine q a
  ≤ Canonical.listLength (Local.rules machine)
fetchConcreteRuleWorkBound machine q a =
  scanRuleWorkBound machine q a (Local.rules machine)

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
--   finite table is the existing ConcreteTapeMachine.rules;
--   successful fetch identifies an actual listed rule;
--   source/read matching is proved from the machine equality deciders;
--   sequential table-fetch work <= |rules|.
--
-- STILL OPEN:
--   turn the selected rule into an executable whole-tape step;
--   prove iteration agrees with Local.MachineStep witnesses;
--   encode arbitrary standard polynomial-time machines into this model with
--   polynomial overhead, and conversely;
--   discover an algorithm-independent SAT lower-bound obstruction.
------------------------------------------------------------------------
