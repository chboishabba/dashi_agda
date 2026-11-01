module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact where

------------------------------------------------------------------------
-- THE ACTUAL SELF-DIAGONAL SHANNON RESTRICTION FAMILY
--
-- P9 must classify only formulas reachable from ONE self-diagonal root, not
-- all SAT instances.
--
-- This owner constructs that domain exactly.
--
-- 1. RestrictionDerivation root current witnesses that current is obtained from
--    root by repeated head restrictions.
--
-- 2. Under an exact SAT oracle, every reachable nonterminal current node obeys
--    the exact Shannon law.
--
-- 3. A SelfDiagonalSemanticWitness supplies an ordinary Clay-critical Cook
--    formula.  The Cook/indexed bridge gives its finite indexed root, and the
--    round-trip theorem proves this indexed root is the SAME Cook syntax when
--    translated back.
--
-- No quotient is postulated here.  This file pays the domain on which a future
-- resource-closing quotient must act.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceBoundedSelfDiagonalExact as Self
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSATShannonSemanticAuthorityExact as Shannon

------------------------------------------------------------------------
-- Reachability under repeated Shannon restrictions.
------------------------------------------------------------------------

data RestrictionDerivation
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) :
    ∀ {currentVariables : Nat} →
    SAT.BooleanFormula currentVariables →
    Set where

  restrictionRoot :
    RestrictionDerivation
      root
      root

  restrictionFalse :
    ∀ {currentVariables : Nat}
      {current : SAT.BooleanFormula (suc currentVariables)} →
    RestrictionDerivation root current →
    RestrictionDerivation
      root
      (SAT.restrictHead false current)

  restrictionTrue :
    ∀ {currentVariables : Nat}
      {current : SAT.BooleanFormula (suc currentVariables)} →
    RestrictionDerivation root current →
    RestrictionDerivation
      root
      (SAT.restrictHead true current)

------------------------------------------------------------------------
-- A reachable node package.
------------------------------------------------------------------------

record RestrictionNode
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor restriction-node
  field
    currentVariables : Nat
    currentFormula :
      SAT.BooleanFormula currentVariables
    derivation :
      RestrictionDerivation
        root
        currentFormula

open RestrictionNode public

rootNode :
  ∀ {variables : Nat}
    (root : SAT.BooleanFormula variables) →
  RestrictionNode root
rootNode {variables} root =
  restriction-node
    variables
    root
    restrictionRoot

falseChild :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula (suc currentVariables)} →
  RestrictionDerivation root current →
  RestrictionNode root
falseChild
    {currentVariables = currentVariables}
    {current = current}
    derivation =
  restriction-node
    currentVariables
    (SAT.restrictHead false current)
    (restrictionFalse derivation)

trueChild :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula (suc currentVariables)} →
  RestrictionDerivation root current →
  RestrictionNode root
trueChild
    {currentVariables = currentVariables}
    {current = current}
    derivation =
  restriction-node
    currentVariables
    (SAT.restrictHead true current)
    (restrictionTrue derivation)

------------------------------------------------------------------------
-- Shannon law holds at every reachable nonterminal node.
------------------------------------------------------------------------

reachableShannonLaw :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula (suc currentVariables)} →
  RestrictionDerivation root current →
  Search.decide oracle current
  ≡
  SAT.orBool
    (Search.decide oracle
      (SAT.restrictHead false current))
    (Search.decide oracle
      (SAT.restrictHead true current))
reachableShannonLaw
    oracle
    {current = current}
    derivation =
  Shannon.satDecisionShannon
    oracle
    current

------------------------------------------------------------------------
-- Pre-fixed-point Cook root.
--
-- This requires ONLY an ordinary Cook formula.  A future intensional
-- self-reference constructor may produce such a formula before its diagonal
-- semantics are established.
------------------------------------------------------------------------

cookIndexedRestrictionRoot :
  (formula : Cook.BooleanFormula) →
  SAT.BooleanFormula
    (Bridge.formulaVariableBound formula)
cookIndexedRestrictionRoot =
  Bridge.cookToIndexed

cookRestrictionRootRoundTrip :
  (formula : Cook.BooleanFormula) →
  Bridge.indexedToCook
    (cookIndexedRestrictionRoot formula)
  ≡ formula
cookRestrictionRootRoundTrip =
  Bridge.indexedAfterCook

cookRestrictionRootNode :
  (formula : Cook.BooleanFormula) →
  RestrictionNode
    (cookIndexedRestrictionRoot formula)
cookRestrictionRootNode formula =
  rootNode
    (cookIndexedRestrictionRoot formula)

------------------------------------------------------------------------
-- Post-fixed-point specialization.
--
-- IMPORTANT DEPENDENCY BOUNDARY:
-- SelfDiagonalSemanticWitness already contains the decisive diagonal semantic
-- equivalence and therefore already yields SATDecisionFailure.  The functions
-- below are useful for diagnostics/transport after such a witness exists, but
-- they MUST NOT be used as the input premise for constructing the P9 quotient.
-- The live pre-fixed-point domain is cookIndexedRestrictionRoot above.
------------------------------------------------------------------------

selfDiagonalIndexedRoot :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness : Self.SelfDiagonalSemanticWitness candidate) →
  SAT.BooleanFormula
    (Bridge.formulaVariableBound
      (Self.formula witness))
selfDiagonalIndexedRoot witness =
  Bridge.cookToIndexed
    (Self.formula witness)

selfDiagonalRootRoundTrip :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness : Self.SelfDiagonalSemanticWitness candidate) →
  Bridge.indexedToCook
    (selfDiagonalIndexedRoot witness)
  ≡
  Self.formula witness
selfDiagonalRootRoundTrip witness =
  Bridge.indexedAfterCook
    (Self.formula witness)

selfDiagonalRootNode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness : Self.SelfDiagonalSemanticWitness candidate) →
  RestrictionNode
    (selfDiagonalIndexedRoot witness)
selfDiagonalRootNode witness =
  rootNode
    (selfDiagonalIndexedRoot witness)

------------------------------------------------------------------------
-- Under SAT in P, the same Clay-critical hypothetical decider induces the
-- exact oracle used at every node of this self-diagonal restriction family.
------------------------------------------------------------------------

selfDiagonalRestrictionOracle :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  SAT.SATDecisionOracle
selfDiagonalRestrictionOracle satP =
  Bridge.indexedOracleFromCookInP satP

------------------------------------------------------------------------
-- Research consequence.
--
-- P9's restriction domain is now real WITHOUT assuming the fixed point:
--
--   candidate Cook formula
--      -> cookIndexedRestrictionRoot
--      -> RestrictionDerivation descendants.
--
-- A future quotient must classify only descendants of the formula produced by
-- a genuine pre-fixed-point intensional constructor.  The specialization from
-- SelfDiagonalSemanticWitness is downstream/diagnostic because that witness
-- already proves a SAT decision failure.
------------------------------------------------------------------------
