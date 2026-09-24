module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunTransitionCompleteExact where

------------------------------------------------------------------------
-- REVERSE COOK--LEVIN: ACTUAL RUN SATISFIES THE GLOBAL TRANSITION CNF
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunInitialCompleteExact as InitialComplete
import DASHI.Mathematics.Complexity.ConcreteTapeEncodedRunSemanticScanExact as EncodedScan
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticCompleteExact as SemanticComplete
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

encodedRunTransitionCNF_complete :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (run : Run.WellFormedTapeRun machine start rows finish) →
  CNF.evaluateCNF
    (Transition.globalTransitionCNF
      stateCoverage symbolCoverage nonempty
      (Run.runLength run)
      (Canonical.listLength (Local.cells start)))
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
  ≡ true
encodedRunTransitionCNF_complete
    stateCoverage symbolCoverage nonempty run =
  SemanticComplete.globalTransitionCNF_complete_of_semanticScan
    stateCoverage symbolCoverage nonempty
    (Run.runLength run)
    (Canonical.listLength (Local.cells _))
    (Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage run)
    (EncodedScan.encodedRunSemanticScan
      stateCoverage symbolCoverage nonempty run)

encodedAcceptingAssignment_transitionBase :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  CNF.evaluateCNF
    (Transition.globalTransitionCNF
      stateCoverage symbolCoverage nonempty
      (Accepting.acceptingRunLength certificate)
      (Canonical.listLength (Local.cells start)))
    (FormulaSem.baseTraceBits
      (Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate))
  ≡ true
encodedAcceptingAssignment_transitionBase
    stateCoverage symbolCoverage nonempty certificate
    rewrite InitialComplete.encodedAcceptingAssignment_baseTrace
      stateCoverage symbolCoverage certificate =
  encodedRunTransitionCNF_complete
    stateCoverage symbolCoverage nonempty
    (Accepting.run certificate)

encodedAcceptingAssignment_transitionLifted :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  CNF.evaluateCNF
    (GlobalCNF.liftTransitionCNF
      stateCoverage symbolCoverage nonempty
      (Accepting.acceptingRunLength certificate)
      (Canonical.listLength (Local.cells start)))
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ true
encodedAcceptingAssignment_transitionLifted
    stateCoverage symbolCoverage nonempty certificate =
  trans
    (Rename.renamedCNFEvaluation
      Endpoint.liftBaseIndex
      transitionFormula assignment)
    (encodedAcceptingAssignment_transitionBase
      stateCoverage symbolCoverage nonempty certificate)
  where
    transitionFormula =
      Transition.globalTransitionCNF
        stateCoverage symbolCoverage nonempty
        (Accepting.acceptingRunLength certificate)
        (Canonical.listLength (Local.cells _))

    assignment =
      Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate

record AcceptingRunTransitionCompleteReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    encodedRunSemanticScanPaid : Bool
    baseTransitionCNFCompletePaid : Bool
    extendedTransitionCNFCompletePaid : Bool

acceptingRunTransitionCompleteReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  AcceptingRunTransitionCompleteReceipt machine
acceptingRunTransitionCompleteReceipt machine = record
  { encodedRunSemanticScanPaid = true
  ; baseTransitionCNFCompletePaid = true
  ; extendedTransitionCNFCompletePaid = true
  }
