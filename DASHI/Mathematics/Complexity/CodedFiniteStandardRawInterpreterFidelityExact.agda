module DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityExact where

------------------------------------------------------------------------
-- RAW SELF-DELIMITING INTERPRETER FIDELITY ON ACTUAL CODED MACHINES
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as Code
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact as Raw
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run

codedPresentation : Coded.CodedFiniteStandardTM → Presented.FinitePresentedStandardTM
codedPresentation = Coded.decodeCodedStandardTM

codedConcrete : Coded.CodedFiniteStandardTM → Local.ConcreteTapeMachine
codedConcrete code =
  Presented.finitePresentedStandardToConcrete (codedPresentation code)

codedStandard :
  (code : Coded.CodedFiniteStandardTM) →
  Standard.StandardSingleTapeMachine
    (Fin.Fin (Coded.stateCount code))
    (Fin.Fin (Coded.symbolCount code))
codedStandard code =
  Presented.finitePresentedStandardMachine (codedPresentation code)

finEqualToNatEqual :
  ∀ {n : Nat} (left right : Fin.Fin n) →
  Coded.finEqual left right
  ≡ Raw.natEqual (Fin.toℕ left) (Fin.toℕ right)
finEqualToNatEqual {suc n} Fin.zero Fin.zero = refl
finEqualToNatEqual {suc n} Fin.zero (Fin.suc right) = refl
finEqualToNatEqual {suc n} (Fin.suc left) Fin.zero = refl
finEqualToNatEqual {suc n} (Fin.suc left) (Fin.suc right) =
  finEqualToNatEqual left right

rawRuleKeyMatchExact :
  ∀ {states symbols : Nat}
    (rule : Local.TapeRule (Fin.Fin states) (Fin.Fin symbols))
    (q : Fin.Fin states)
    (a : Fin.Fin symbols) →
  Raw.ruleKeyMatches (Code.rawRule rule) (Fin.toℕ q) (Fin.toℕ a)
  ≡
  Raw.andBool
    (Coded.finEqual (Local.sourceState rule) q)
    (Coded.finEqual (Local.readSymbol rule) a)
rawRuleKeyMatchExact rule q a
  rewrite finEqualToNatEqual (Local.sourceState rule) q
        | finEqualToNatEqual (Local.readSymbol rule) a = refl

matchedRaw :
  ∀ {code : Coded.CodedFiniteStandardTM}
    {q : Fin.Fin (Coded.stateCount code)}
    {a : Fin.Fin (Coded.symbolCount code)}
    {rules : List
      (Local.TapeRule
        (Fin.Fin (Coded.stateCount code))
        (Fin.Fin (Coded.symbolCount code)))} →
  Maybe (Interpreter.MatchedRule (codedConcrete code) q a rules) →
  Maybe Code.RawRule
matchedRaw nothing = nothing
matchedRaw (just matched) = just (Code.rawRule (Interpreter.rule matched))

scanRawRulesExact :
  (code : Coded.CodedFiniteStandardTM)
  (q : Fin.Fin (Coded.stateCount code))
  (a : Fin.Fin (Coded.symbolCount code))
  (rules : List
    (Local.TapeRule
      (Fin.Fin (Coded.stateCount code))
      (Fin.Fin (Coded.symbolCount code)))) →
  Raw.fetchRawRule
    (Code.rawRules rules)
    (Fin.toℕ q)
    (Fin.toℕ a)
  ≡
  matchedRaw (Interpreter.scanRuleTable (codedConcrete code) q a rules)
scanRawRulesExact code q a [] = refl
scanRawRulesExact code q a (rule ∷ rest)
  with Coded.finEqual (Local.sourceState rule) q
     | Coded.finEqual (Local.readSymbol rule) a
... | true | true
  rewrite rawRuleKeyMatchExact rule q a = refl
... | true | false
  rewrite rawRuleKeyMatchExact rule q a
        | scanRawRulesExact code q a rest = refl
... | false | true
  rewrite rawRuleKeyMatchExact rule q a
        | scanRawRulesExact code q a rest = refl
... | false | false
  rewrite rawRuleKeyMatchExact rule q a
        | scanRawRulesExact code q a rest = refl

fetchRawActualExact :
  (code : Coded.CodedFiniteStandardTM)
  (q : Fin.Fin (Coded.stateCount code))
  (a : Fin.Fin (Coded.symbolCount code)) →
  Raw.fetchRawRule
    (Code.rules (Code.rawMachineView code))
    (Fin.toℕ q)
    (Fin.toℕ a)
  ≡
  matchedRaw (Interpreter.fetchConcreteRule (codedConcrete code) q a)
fetchRawActualExact code q a =
  scanRawRulesExact code q a (Coded.rules code)

finListToNat : ∀ {n : Nat} → List (Fin.Fin n) → List Nat
finListToNat [] = []
finListToNat (x ∷ xs) = Fin.toℕ x ∷ finListToNat xs

rawConfigurationOf :
  ∀ {code : Coded.CodedFiniteStandardTM} →
  Standard.StandardConfiguration (codedStandard code) →
  Raw.RawConfiguration
rawConfigurationOf
    (Standard.standard-configuration left q scanned right) =
  Raw.raw-configuration
    (finListToNat left)
    (Fin.toℕ q)
    (Fin.toℕ scanned)
    (finListToNat right)

mapMaybeConfiguration :
  ∀ {code : Coded.CodedFiniteStandardTM} →
  Maybe (Standard.StandardConfiguration (codedStandard code)) →
  Maybe Raw.RawConfiguration
mapMaybeConfiguration nothing = nothing
mapMaybeConfiguration (just configuration) =
  just (rawConfigurationOf configuration)

rawApplyRuleExact :
  ∀ {code : Coded.CodedFiniteStandardTM}
    (configuration : Standard.StandardConfiguration (codedStandard code))
    (rule : Local.TapeRule
      (Fin.Fin (Coded.stateCount code))
      (Fin.Fin (Coded.symbolCount code))) →
  Raw.applyRawRule
    (Code.rawMachineView code)
    (rawConfigurationOf configuration)
    (Code.rawRule rule)
  ≡
  just
    (rawConfigurationOf
      (Standard.standardApplyTransition
        (codedStandard code)
        configuration
        (Standard.standard-transition
          (Local.targetState rule)
          (Local.writeSymbol rule)
          (Local.direction rule))))
rawApplyRuleExact
    (Standard.standard-configuration [] q scanned right)
    (Local.tape-rule source read target write Local.moveLeft) = refl
rawApplyRuleExact
    (Standard.standard-configuration (near ∷ left) q scanned right)
    (Local.tape-rule source read target write Local.moveLeft) = refl
rawApplyRuleExact
    (Standard.standard-configuration left q scanned right)
    (Local.tape-rule source read target write Local.stayPut) = refl
rawApplyRuleExact
    (Standard.standard-configuration left q scanned [])
    (Local.tape-rule source read target write Local.moveRight) = refl
rawApplyRuleExact
    (Standard.standard-configuration left q scanned (next ∷ right))
    (Local.tape-rule source read target write Local.moveRight) = refl

rawNextExact :
  (code : Coded.CodedFiniteStandardTM)
  (configuration : Standard.StandardConfiguration (codedStandard code)) →
  Raw.rawNext
    (Code.rawMachineView code)
    (rawConfigurationOf configuration)
  ≡
  mapMaybeConfiguration (Standard.standardNext (codedStandard code) configuration)
rawNextExact code configuration
  with Interpreter.fetchConcreteRule
    (codedConcrete code)
    (Standard.state configuration)
    (Standard.scanned configuration)
... | nothing
  rewrite fetchRawActualExact
    code (Standard.state configuration) (Standard.scanned configuration) = refl
... | just matched
  rewrite fetchRawActualExact
    code (Standard.state configuration) (Standard.scanned configuration)
        | rawApplyRuleExact configuration (Interpreter.rule matched) = refl

rawNextOfStandardStep :
  (code : Coded.CodedFiniteStandardTM)
  {current next : Standard.StandardConfiguration (codedStandard code)} →
  Standard.standardNext (codedStandard code) current ≡ just next →
  Raw.rawNext
    (Code.rawMachineView code)
    (rawConfigurationOf current)
  ≡ just (rawConfigurationOf next)
rawNextOfStandardStep code {current} {next} edge =
  trans
    (rawNextExact code current)
    (cong mapMaybeConfiguration edge)

rawIterateFollowsStandardRun :
  (code : Coded.CodedFiniteStandardTM)
  ∀ {steps : Nat}
    {start finish : Standard.StandardConfiguration (codedStandard code)} →
  Run.StandardExactRun (codedStandard code) steps start finish →
  Raw.iterateRaw
    steps
    (Code.rawMachineView code)
    (rawConfigurationOf start)
  ≡ just (rawConfigurationOf finish)
rawIterateFollowsStandardRun code Run.standardRunDone = refl
rawIterateFollowsStandardRun code
    (Run.standardRunStep edge rest)
  rewrite rawNextOfStandardStep code edge
        | rawIterateFollowsStandardRun code rest = refl

selfDelimitedInterpreterFollowsStandardRun :
  (code : Coded.CodedFiniteStandardTM)
  ∀ {steps : Nat}
    {start finish : Standard.StandardConfiguration (codedStandard code)} →
  Run.StandardExactRun (codedStandard code) steps start finish →
  Raw.runSelfDelimitedCode
    steps
    (Code.selfDelimitingMachineCode code)
    (rawConfigurationOf start)
  ≡ just (rawConfigurationOf finish)
selfDelimitedInterpreterFollowsStandardRun code run
  rewrite Raw.runActualCodeReducesToRawView
    _ code _ =
  rawIterateFollowsStandardRun code run

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The untyped self-delimiting interpreter is now faithful on every actual coded
-- standard-machine run, edge-for-edge and with identical step count.  It is a
-- semantic normalization of the existing machine, not a second machine model.
-- The remaining universal-route implementation is to compile this one fixed
-- first-order parser/scan/update recursion into a literal coded standard TM.
------------------------------------------------------------------------
