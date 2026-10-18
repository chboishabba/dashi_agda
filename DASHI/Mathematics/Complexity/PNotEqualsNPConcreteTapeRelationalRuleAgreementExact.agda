module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRelationalRuleAgreementExact where

------------------------------------------------------------------------
-- FIRST-MATCH EXECUTABLE RULE = RELATIONAL WELL-FORMED STEP RULE
--
-- A WellFormedMachineStep already determines the source state and read symbol
-- appearing in its centered rule window.  Under the repository's existing
-- RuleDispatchUnique predicate, the sequential first-match interpreter must
-- therefore return exactly that relational rule.
--
-- This is the semantic core of executable <-> relational equivalence.  The
-- only remaining converse seam after this file is transporting the resulting
-- after-row construction through the relational occurrence equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism

------------------------------------------------------------------------
-- For the intrinsic before-row view reconstructed from a relational step,
-- literal first-match lookup returns that step's actual listed rule.
------------------------------------------------------------------------

firstMatchAgreesWithWellFormedStepRule :
  ∀ {machine before after}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  let interior = Character.wellFormedStepBeforeInterior wellFormed
      wanted = Local.rule (WF.step wellFormed)
  in
  Σ (Interpreter.MatchedRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
      (Local.rules machine))
    (λ matched →
      Interpreter.fetchConcreteRule
        machine
        (Character.headState interior)
        (Character.readSymbol interior)
        ≡ just matched
      × Interpreter.rule matched ≡ wanted)
firstMatchAgreesWithWellFormedStepRule
    {machine} deterministic wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left =
  Determinism.fetchConcreteRuleCompleteUnique
    deterministic
    (Local.ruleOccursInMachine (WF.step wellFormed))
    refl refl
... | Local.realizes-stay =
  Determinism.fetchConcreteRuleCompleteUnique
    deterministic
    (Local.ruleOccursInMachine (WF.step wellFormed))
    refl refl
... | Local.realizes-right =
  Determinism.fetchConcreteRuleCompleteUnique
    deterministic
    (Local.ruleOccursInMachine (WF.step wellFormed))
    refl refl

------------------------------------------------------------------------
-- A failed first-match lookup is incompatible with any relational
-- WellFormedMachineStep from the same intrinsic before-row configuration.
------------------------------------------------------------------------

wellFormedStepForcesExecutableRule :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  let interior = Character.wellFormedStepBeforeInterior wellFormed
  in
  Σ (Interpreter.MatchedRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
      (Local.rules machine))
    (λ matched →
      Interpreter.fetchConcreteRule
        machine
        (Character.headState interior)
        (Character.readSymbol interior)
        ≡ just matched)
wellFormedStepForcesExecutableRule {machine} wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left =
  Determinism.fetchConcreteRuleComplete
    machine _ _
    (Local.rule (WF.step wellFormed))
    (Local.ruleOccursInMachine (WF.step wellFormed))
    refl refl
... | Local.realizes-stay =
  Determinism.fetchConcreteRuleComplete
    machine _ _
    (Local.rule (WF.step wellFormed))
    (Local.ruleOccursInMachine (WF.step wellFormed))
    refl refl
... | Local.realizes-right =
  Determinism.fetchConcreteRuleComplete
    machine _ _
    (Local.rule (WF.step wellFormed))
    (Local.ruleOccursInMachine (WF.step wellFormed))
    refl refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
-- * every relational well-formed step guarantees executable lookup succeeds;
-- * under RuleDispatchUnique, first-match returns the exact relational rule;
-- * duplicate-key ambiguity is therefore completely removed at rule level.
--
-- NEXT LOCAL CLOSURE:
-- * transport `Window.afterRowForRule` through the relational
--   `WindowRewriteOccurrence.afterShape` equality to prove exact after-row
--   equality and hence executable iff relational semantics.
--
-- AFTER THAT:
-- * standard deterministic TM <-> ConcreteTapeMachine polynomial simulation.
------------------------------------------------------------------------
