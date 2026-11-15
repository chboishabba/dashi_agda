module DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact where

------------------------------------------------------------------------
-- ONE SATISFYING GLOBAL FORMULA -> THREE SEMANTIC DECODE OBLIGATIONS
--
-- From the final Cook--Levin CNF we extract:
--   (1) the base transition conjunction is true on the base trace prefix;
--   (2) row 0 bits are exactly the prescribed fixed-width input target;
--   (3) the final row contains a decoded accepting-state cell.
--
-- What remains above this file is to turn (1) into adjacent decoded semantic
-- transitions and then assemble those rows into the existing accepting-run
-- carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceEndpointSoundExact as AcceptSound
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

baseTraceBits :
  ∀ {machine steps cols} →
  CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols) →
  CNF.Bits (Trace.GlobalTraceWidth machine steps cols)
baseTraceBits {machine} {steps} {cols} assignment =
  Rename.pullbackBits (Endpoint.liftBaseIndex {machine} {steps} {cols}) assignment

record SatisfyingGlobalFormulaSemantics
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where
  field
    transitionCNFTrue :
      CNF.evaluateCNF
        (Transition.globalTransitionCNF
          stateCoverage symbolCoverage nonempty steps cols)
        (baseTraceBits {machine} {steps} {cols} assignment)
      ≡ true

    initialRowBitsExact :
      Rename.pullbackBits
        (Endpoint.initialRowExtendedRename {machine} {steps} {cols})
        assignment
      ≡ initialTarget

    acceptingFinalCell :
      AcceptSound.DecodedAcceptingCell {machine} {steps} {cols}
        stateCoverage symbolCoverage assignment

open SatisfyingGlobalFormulaSemantics public

satisfyingGlobalFormulaSemantics :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.evaluateCNF
    (GlobalCNF.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps cols initialTarget)
    assignment
  ≡ true →
  SatisfyingGlobalFormulaSemantics
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget assignment
satisfyingGlobalFormulaSemantics {machine}
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget assignment accepted =
  record
    { transitionCNFTrue = transitionTrueBase
    ; initialRowBitsExact =
        Endpoint._↔_.to
          (Endpoint.initialEndpointCNF_iff {machine} {steps} {cols}
            initialTarget assignment)
          (GlobalCNF.initialTrue parts)
    ; acceptingFinalCell =
        AcceptSound.acceptingEndpointCNF_sound {machine} {steps} {cols}
          stateCoverage symbolCoverage assignment
          (GlobalCNF.acceptingTrue parts)
    }
  where
    parts =
      GlobalCNF.globalCookLevinCNFSoundParts
        stateCoverage symbolCoverage nonempty
        steps cols initialTarget assignment accepted

    transitionFormula =
      Transition.globalTransitionCNF
        stateCoverage symbolCoverage nonempty steps cols

    renamedEvaluation =
      Rename.renamedCNFEvaluation
        (Endpoint.liftBaseIndex {machine} {steps} {cols})
        transitionFormula
        assignment

    transitionTrueBase :
      CNF.evaluateCNF
        transitionFormula
        (baseTraceBits {machine} {steps} {cols} assignment)
      ≡ true
    transitionTrueBase =
      trans (sym renamedEvaluation) (GlobalCNF.transitionTrue parts)

record GlobalFormulaSemanticReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    satisfyingFormulaToTransitionCNFPaid : Bool
    satisfyingFormulaToExactInitialBitsPaid : Bool
    satisfyingFormulaToDecodedAcceptingCellPaid : Bool
    transitionCNFToDecodedSemanticStepsPaid : Bool
    decodedStepsToRunPaid : Bool
    initialBitsToLiteralInputRowPaid : Bool
    acceptingCellToAcceptingRunEndpointPaid : Bool
    satIffAcceptingRunPaid : Bool

globalFormulaSemanticReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalFormulaSemanticReceipt machine
globalFormulaSemanticReceipt machine = record
  { satisfyingFormulaToTransitionCNFPaid = true
  ; satisfyingFormulaToExactInitialBitsPaid = true
  ; satisfyingFormulaToDecodedAcceptingCellPaid = true
  ; transitionCNFToDecodedSemanticStepsPaid = false
  ; decodedStepsToRunPaid = false
  ; initialBitsToLiteralInputRowPaid = false
  ; acceptingCellToAcceptingRunEndpointPaid = false
  ; satIffAcceptingRunPaid = false
  }
