module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunGlobalCompleteExact where

------------------------------------------------------------------------
-- REVERSE COOK--LEVIN CAPSTONE:
-- ACTUAL ACCEPTING RUN -> ONE SATISFYING GLOBAL COOK--LEVIN ASSIGNMENT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunTransitionCompleteExact as TransitionComplete
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunInitialCompleteExact as InitialComplete
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAcceptCompleteExact as AcceptComplete
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

acceptingRunGlobalPartsTrue :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  GlobalCNF.GlobalFormulaPartsTrue
    stateCoverage symbolCoverage nonempty
    (Accepting.acceptingRunLength certificate)
    (Canonical.listLength (Local.cells start))
    (Flat.encodeRow stateCoverage symbolCoverage start)
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
acceptingRunGlobalPartsTrue
    stateCoverage symbolCoverage nonempty certificate =
  record
    { GlobalCNF.transitionTrue =
        TransitionComplete.encodedAcceptingAssignment_transitionLifted
          stateCoverage symbolCoverage nonempty certificate
    ; GlobalCNF.initialTrue =
        InitialComplete.encodedAcceptingAssignment_initialPullback
          stateCoverage symbolCoverage certificate
    ; GlobalCNF.acceptingTrue =
        AcceptComplete.acceptingEndpointCNF_complete_for_run
          stateCoverage symbolCoverage certificate
    }

acceptingRunSatisfiesGlobalCookLevinCNF :
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
    (GlobalCNF.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      (Accepting.acceptingRunLength certificate)
      (Canonical.listLength (Local.cells start))
      (Flat.encodeRow stateCoverage symbolCoverage start))
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ true
acceptingRunSatisfiesGlobalCookLevinCNF
    stateCoverage symbolCoverage nonempty certificate =
  GlobalCNF.globalCookLevinCNFCompleteParts
    stateCoverage symbolCoverage nonempty
    (Accepting.acceptingRunLength certificate)
    (Canonical.listLength (Local.cells _))
    (Flat.encodeRow stateCoverage symbolCoverage _)
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
    (acceptingRunGlobalPartsTrue
      stateCoverage symbolCoverage nonempty certificate)

record AcceptingRunGlobalCompleteReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    transitionCompletePaid : Bool
    initialCompletePaid : Bool
    acceptingCompletePaid : Bool
    wholeGlobalFormulaCompletePaid : Bool

acceptingRunGlobalCompleteReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  AcceptingRunGlobalCompleteReceipt machine
acceptingRunGlobalCompleteReceipt machine = record
  { transitionCompletePaid = true
  ; initialCompletePaid = true
  ; acceptingCompletePaid = true
  ; wholeGlobalFormulaCompletePaid = true
  }
