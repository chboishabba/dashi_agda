module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunDecodeExact where

------------------------------------------------------------------------
-- CANONICAL RUN ENCODING DECODES BACK TO THE LITERAL RUN
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact as Initial
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

runRows :
  ∀ {machine start rows finish} →
  Run.WellFormedTapeRun machine start rows finish →
  List (Local.TapeRow machine)
runRows {start = start} Run.runDone =
  start ∷ []
runRows {start = current}
    (Run.runStep {next = next} step rest) =
  current ∷ runRows rest

runRuleChoices :
  ∀ {machine start rows finish} →
  Run.WellFormedTapeRun machine start rows finish →
  List (Selector.ListedRule (Local.rules machine))
runRuleChoices Run.runDone =
  []
runRuleChoices (Run.runStep step rest) =
  Selector.listed-rule
    (Local.rule (WF.step step))
    (Local.ruleOccursInMachine (WF.step step))
  ∷ runRuleChoices rest

decodeRunRows_encodeRunRows :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Decode.decodeRows
    stateCoverage symbolCoverage
    (suc (Run.runLength run))
    (Canonical.listLength (Local.cells start))
    (Assignment.encodeRunRows
      stateCoverage symbolCoverage run)
  ≡ runRows run
decodeRunRows_encodeRunRows
    stateCoverage symbolCoverage Run.runDone
    rewrite Initial.decodeRow_encodeRow
      stateCoverage symbolCoverage _ =
  refl
decodeRunRows_encodeRunRows {machine} {start = current}
    stateCoverage symbolCoverage
    (Run.runStep {next = next} step rest)
    rewrite Assignment.stepCanonicalLength step
          | Canonical.takeAppendBits
              (Flat.encodeRow stateCoverage symbolCoverage current)
              (Assignment.encodeRunRows
                stateCoverage symbolCoverage rest)
          | Canonical.dropAppendBits
              (Flat.encodeRow stateCoverage symbolCoverage current)
              (Assignment.encodeRunRows
                stateCoverage symbolCoverage rest)
          | Initial.decodeRow_encodeRow
              stateCoverage symbolCoverage current
          | decodeRunRows_encodeRunRows
              stateCoverage symbolCoverage rest =
  refl
  where
    import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat

decodeRuleChoice_encodeRuleOccurs :
  ∀ {machine}
    (nonempty : Selector.NonemptyRuleTable machine)
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (occurrence :
      Local.RuleOccurs rule (Local.rules machine)) →
  Selector.decodeRuleChoice nonempty
    (Selector.encodeRuleOccurs occurrence)
  ≡ Selector.listed-rule rule occurrence
decodeRuleChoice_encodeRuleOccurs
    nonempty occurrence
    rewrite Selector.decodePresentEncode occurrence =
  refl

decodeRunSelectors_encodeRunSelectors :
  ∀ {machine start rows finish}
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Trace.decodeSelectors nonempty
    (Run.runLength run)
    (Assignment.encodeRunSelectors run)
  ≡ runRuleChoices run
decodeRunSelectors_encodeRunSelectors
    nonempty Run.runDone =
  refl
decodeRunSelectors_encodeRunSelectors
    {machine} nonempty
    (Run.runStep step rest)
    rewrite Canonical.takeAppendBits
      (Selector.encodeRuleOccurs
        (Local.ruleOccursInMachine (WF.step step)))
      (Assignment.encodeRunSelectors rest)
          | Canonical.dropAppendBits
              (Selector.encodeRuleOccurs
                (Local.ruleOccursInMachine (WF.step step)))
              (Assignment.encodeRunSelectors rest)
          | decodeRuleChoice_encodeRuleOccurs
              nonempty
              (Local.ruleOccursInMachine (WF.step step))
          | decodeRunSelectors_encodeRunSelectors
              nonempty rest =
  refl

record AcceptingRunDecodeReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    canonicalRowsDecodePaid : Agda.Builtin.Bool.Bool
    canonicalSelectorsDecodePaid : Agda.Builtin.Bool.Bool
    decodedTraceMatchesLiteralRunPaid : Agda.Builtin.Bool.Bool

acceptingRunDecodeReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  AcceptingRunDecodeReceipt machine
acceptingRunDecodeReceipt machine = record
  { canonicalRowsDecodePaid = Agda.Builtin.Bool.true
  ; canonicalSelectorsDecodePaid = Agda.Builtin.Bool.true
  ; decodedTraceMatchesLiteralRunPaid = Agda.Builtin.Bool.true
  }
