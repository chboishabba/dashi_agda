module DASHI.Mathematics.Complexity.PNotEqualsNPSATTruthQuotientConstructionCostExact where

------------------------------------------------------------------------
-- TWO-CLASS SAT TRUTH QUOTIENT: EXACT CONSTRUCTOR RECURSION COST
--
-- Companion:
--   PNotEqualsNPSATTruthQuotientCircularityExact
--
-- Truth-only semantic quotienting has only two classes if one computes the SAT
-- bit itself.  The repository's constructive exact SAT decider does exactly
-- that by recursively exploring both restrictions.
--
-- This owner counts the structural leaves of that classifier construction.
--
-- For every n-variable formula:
--
--   leaves = 2^n.
--
-- So a tiny quotient IMAGE says nothing about cheap constructibility.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT

------------------------------------------------------------------------
-- Structural recursion tree of the exact finite SAT classifier.
------------------------------------------------------------------------

truthClassifierLeaves :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  Nat
truthClassifierLeaves {zero} formula =
  suc zero
truthClassifierLeaves {suc variables} formula =
  truthClassifierLeaves
    (SAT.restrictHead false formula)
  +
  truthClassifierLeaves
    (SAT.restrictHead true formula)

pow2 : Nat → Nat
pow2 zero =
  suc zero
pow2 (suc exponent) =
  pow2 exponent + pow2 exponent

truthClassifierLeavesExact :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  truthClassifierLeaves formula
  ≡ pow2 variables
truthClassifierLeavesExact {zero} formula =
  refl
truthClassifierLeavesExact {suc variables} formula
    rewrite
      truthClassifierLeavesExact
        (SAT.restrictHead false formula)
      |
      truthClassifierLeavesExact
        (SAT.restrictHead true formula) =
  refl

------------------------------------------------------------------------
-- Research consequence.
--
-- The canonical exact two-class quotient has:
--
--   output width:  1 bit
--   image size:    at most 2 classes
--   naive exact construction tree: 2^n leaves
--
-- Hence P9 must control construction complexity directly.  Small semantic
-- image/cardinality by itself is not evidence of a useful self-diagonal
-- quotient.
------------------------------------------------------------------------
