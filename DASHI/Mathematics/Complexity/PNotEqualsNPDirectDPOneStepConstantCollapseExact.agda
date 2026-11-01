module DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPOneStepConstantCollapseExact where

------------------------------------------------------------------------
-- ONE SUCCESSFUL DIRECT-DP STEP COLLAPSES THE FORMULA TO A LITERAL CONSTANT
--
-- The preferred direct-DP recurrence computes the exact SAT bit of the current
-- quotient and stores that bit as the next Cook formula:
--
--   next.currentFormula = constant(rootTruth).
--
-- Therefore every successful step lands in a one-node / zero-variable formula.
-- Any high residual-width obstruction must attach BEFORE that first successful
-- Q1 step.  It cannot hide in later recursive states or in the terminal output
-- reached after a successful step.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as Authority

------------------------------------------------------------------------
-- Literal next formula.
------------------------------------------------------------------------

directDPNextFormulaIsConstant :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Q2.currentFormula
      (DirectDP.directDPNextState run)
  ≡
  Cook.constant
    (Authority.arityTerminalRootTruth
      (DirectDP.candidate run)
      (DirectDP.localAdmission run))
directDPNextFormulaIsConstant run =
  refl

directDPNextFormulaNodeCount :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Size.formulaNodeCount
      (Q2.currentFormula
        (DirectDP.directDPNextState run))
  ≡
  suc zero
directDPNextFormulaNodeCount run =
  refl

directDPNextFormulaVariableBound :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Bridge.formulaVariableBound
      (Q2.currentFormula
        (DirectDP.directDPNextState run))
  ≡
  zero
directDPNextFormulaVariableBound run =
  refl

directDPNextIndexedFormulaIsConstant :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Bridge.cookToIndexed
      (Q2.currentFormula
        (DirectDP.directDPNextState run))
  ≡
  SAT.constant
    (Authority.arityTerminalRootTruth
      (DirectDP.candidate run)
      (DirectDP.localAdmission run))
directDPNextIndexedFormulaIsConstant run =
  refl

------------------------------------------------------------------------
-- Consequence for residual width: after a successful step there are no free
-- variables.  Thus any exponential-width falsification must be witnessed on
-- the predecessor state itself.
------------------------------------------------------------------------

directDPHighWidthMustPrecedeFirstSuccess :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Bridge.formulaVariableBound
      (Q2.currentFormula
        (DirectDP.directDPNextState run))
  ≡ zero
directDPHighWidthMustPrecedeFirstSuccess =
  directDPNextFormulaVariableBound

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- This localizes the search:
--
--   initial/live self-instantiation formula
--       -- Q1 quotient construction is the hard step -->
--   literal constant
--       -- no further high-width structure -->
--   termination.
--
-- Therefore equality/high-width transport should target the CURRENT live root,
-- not canonicalTerminalFormula.  The terminal-output route is structurally too
-- late: one successful direct-DP step has already erased all variables.
------------------------------------------------------------------------
