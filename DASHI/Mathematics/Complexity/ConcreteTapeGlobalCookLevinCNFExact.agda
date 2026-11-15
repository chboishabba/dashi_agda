module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact where

------------------------------------------------------------------------
-- ONE GLOBAL COOK--LEVIN CNF
--
-- Formula over the extended trace vector:
--
--   lifted transition conjunction
--   ∧ initial-row exact unit clauses
--   ∧ accepting-endpoint witness clauses
--
-- This file pays the literal finite formula assembly and the Boolean
-- decomposition theorem.  Semantic SAT <-> accepting-run conversion remains
-- a separate theorem above endpoint soundness and decoded-transition soundness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

liftTransitionCNF :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols)
liftTransitionCNF {machine}
    stateCoverage symbolCoverage nonempty steps cols =
  Rename.renameCNF
    (Endpoint.liftBaseIndex {machine} {steps} {cols})
    (Transition.globalTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)

globalCookLevinCNF :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  CNF.Bits (Decode.RowBitsWidth machine cols) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols)
globalCookLevinCNF {machine}
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget =
  Placed.append
    (liftTransitionCNF {machine}
      stateCoverage symbolCoverage nonempty steps cols)
    (Placed.append
      (Endpoint.initialEndpointCNF {machine} {steps} {cols} initialTarget)
      (Endpoint.acceptingEndpointCNF {machine} {steps} {cols}
        stateCoverage symbolCoverage))

record GlobalFormulaPartsTrue
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (assignment : CNF.Bits
      (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where
  field
    transitionTrue :
      CNF.evaluateCNF
        (liftTransitionCNF {machine}
          stateCoverage symbolCoverage nonempty steps cols)
        assignment
      ≡ true

    initialTrue :
      CNF.evaluateCNF
        (Endpoint.initialEndpointCNF {machine} {steps} {cols} initialTarget)
        assignment
      ≡ true

    acceptingTrue :
      CNF.evaluateCNF
        (Endpoint.acceptingEndpointCNF {machine} {steps} {cols}
          stateCoverage symbolCoverage)
        assignment
      ≡ true

open GlobalFormulaPartsTrue public

andTrueLeft :
  ∀ left right →
  CNF.andBool left right ≡ true →
  left ≡ true
andTrueLeft false right ()
andTrueLeft true right proof = refl

andTrueRight :
  ∀ left right →
  CNF.andBool left right ≡ true →
  right ≡ true
andTrueRight false right ()
andTrueRight true right proof = proof

globalCookLevinCNFSoundParts :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (assignment : CNF.Bits
      (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.evaluateCNF
    (globalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps cols initialTarget)
    assignment
  ≡ true →
  GlobalFormulaPartsTrue
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget assignment
globalCookLevinCNFSoundParts {machine}
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget assignment accepted =
  record
    { transitionTrue =
        andTrueLeft transitionValue endpointsValue outer
    ; initialTrue =
        andTrueLeft initialValue acceptingValue inner
    ; acceptingTrue =
        andTrueRight initialValue acceptingValue inner
    }
  where
    transitionFormula =
      liftTransitionCNF {machine}
        stateCoverage symbolCoverage nonempty steps cols

    initialFormula =
      Endpoint.initialEndpointCNF {machine} {steps} {cols} initialTarget

    acceptingFormula =
      Endpoint.acceptingEndpointCNF {machine} {steps} {cols}
        stateCoverage symbolCoverage

    transitionValue =
      CNF.evaluateCNF transitionFormula assignment

    initialValue =
      CNF.evaluateCNF initialFormula assignment

    acceptingValue =
      CNF.evaluateCNF acceptingFormula assignment

    endpointsValue =
      CNF.andBool initialValue acceptingValue

    outer :
      CNF.andBool transitionValue endpointsValue ≡ true
    outer =
      subst (_≡ true)
        (trans
          (Placed.evaluateCNFAppend
            transitionFormula
            (Placed.append initialFormula acceptingFormula)
            assignment)
          (cong (CNF.andBool transitionValue)
            (Placed.evaluateCNFAppend
              initialFormula acceptingFormula assignment)))
        accepted

    inner :
      CNF.andBool initialValue acceptingValue ≡ true
    inner =
      andTrueRight transitionValue endpointsValue outer

globalCookLevinCNFCompleteParts :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (assignment : CNF.Bits
      (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  GlobalFormulaPartsTrue
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget assignment →
  CNF.evaluateCNF
    (globalCookLevinCNF {machine}
      stateCoverage symbolCoverage nonempty
      steps cols initialTarget)
    assignment
  ≡ true
globalCookLevinCNFCompleteParts {machine}
    stateCoverage symbolCoverage nonempty
    steps cols initialTarget assignment parts =
  trans
    (Placed.evaluateCNFAppend
      (liftTransitionCNF {machine}
        stateCoverage symbolCoverage nonempty steps cols)
      (Placed.append
        (Endpoint.initialEndpointCNF {machine} {steps} {cols} initialTarget)
        (Endpoint.acceptingEndpointCNF {machine} {steps} {cols}
          stateCoverage symbolCoverage))
      assignment)
    (trans
      (cong₂ CNF.andBool
        (transitionTrue parts)
        (Placed.evaluateCNFAppend
          (Endpoint.initialEndpointCNF {machine} {steps} {cols} initialTarget)
          (Endpoint.acceptingEndpointCNF {machine} {steps} {cols}
            stateCoverage symbolCoverage)
          assignment))
      (cong (CNF.andBool true)
        (cong₂ CNF.andBool (initialTrue parts) (acceptingTrue parts))))

record GlobalCookLevinCNFReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    transitionCNFLiftPaid : Bool
    transitionInitialAcceptingConjunctionPaid : Bool
    formulaSoundDecompositionPaid : Bool
    formulaCompleteCompositionPaid : Bool
    initialEndpointSemanticSoundPaid : Bool
    acceptingEndpointSemanticSoundPaid : Bool
    decodedTransitionSemanticSoundPaid : Bool
    satIffAcceptingRunPaid : Bool
    polynomialVariableBoundPaid : Bool
    polynomialClauseBoundPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

globalCookLevinCNFReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalCookLevinCNFReceipt machine
globalCookLevinCNFReceipt machine = record
  { transitionCNFLiftPaid = true
  ; transitionInitialAcceptingConjunctionPaid = true
  ; formulaSoundDecompositionPaid = true
  ; formulaCompleteCompositionPaid = true
  ; initialEndpointSemanticSoundPaid = false
  ; acceptingEndpointSemanticSoundPaid = false
  ; decodedTransitionSemanticSoundPaid = false
  ; satIffAcceptingRunPaid = false
  ; polynomialVariableBoundPaid = false
  ; polynomialClauseBoundPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
