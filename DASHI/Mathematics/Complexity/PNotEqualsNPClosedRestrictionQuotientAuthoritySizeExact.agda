module DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientAuthoritySizeExact where

------------------------------------------------------------------------
-- CLOSED QUOTIENT -> LITERAL COOK AUTHORITY SIZE BOUND
--
-- Existing exact results:
--
--   quotientCircuitGateCount:
--     |C_Q| = (rootVariables + 1) * stateCount
--
--   sharedAcceptanceFormulaNodeCountUpper:
--     |Tseitin(C)| <= sharedAcceptanceUpperBound(|C|)
--
--   closedQuotientSATAuthority:
--     the structurally closed quotient compiles to exactly that shared
--     acceptance formula, with root SAT semantics and no D-labelled states.
--
-- This owner composes those quantitative facts:
--
--   |closedAuthority|
--      <=
--   sharedAcceptanceUpperBound
--     ((rootVariables + 1) * stateCount).
--
-- It then exposes the actual self-size budget condition on the ordinary Cook
-- formula, rather than merely on the quotient graph or DP table.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientCircuitExact as QCircuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedUpperBoundExact as SharedUpper

------------------------------------------------------------------------
-- Canonical quotient extracted from the closed package.
------------------------------------------------------------------------

closedQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Closed.ClosedStrictRepresentativeQuotient root →
  Quotient.RestrictionSemanticQuotient root
closedQuotient closed =
  Strict.quotient
    (Closed.strictQuotient closed)

------------------------------------------------------------------------
-- Exact gate count of the quotient circuit.
------------------------------------------------------------------------

closedQuotientCircuitGateCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  QCircuit.Circuit.circuitSize
    (QCircuit.quotientCircuit
      (closedQuotient closed)
      (Closed.closedStateTruth closed))
  ≡
  suc rootVariables
    * Quotient.stateCount
        (closedQuotient closed)
closedQuotientCircuitGateCount
    closed =
  QCircuit.quotientCircuitGateCount
    (closedQuotient closed)
    (Closed.closedStateTruth closed)

------------------------------------------------------------------------
-- Main literal Cook-formula upper bound.
------------------------------------------------------------------------

closedAuthorityNodeCountUpper :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Size.formulaNodeCount
    (Authority.closedQuotientSATAuthority closed)
  ≤
  SharedUpper.sharedAcceptanceUpperBound
    (suc rootVariables
      * Quotient.stateCount
          (closedQuotient closed))
closedAuthorityNodeCountUpper
    {rootVariables}
    closed =
  subst
    (λ gateCount →
      Size.formulaNodeCount
        (Authority.closedQuotientSATAuthority closed)
      ≤
      SharedUpper.sharedAcceptanceUpperBound
        gateCount)
    (closedQuotientCircuitGateCount closed)
    sharedBound
  where
    sharedBound :
      Size.formulaNodeCount
        (Authority.closedQuotientSATAuthority closed)
      ≤
      SharedUpper.sharedAcceptanceUpperBound
        (QCircuit.Circuit.circuitSize
          (QCircuit.quotientCircuit
            (closedQuotient closed)
            (Closed.closedStateTruth closed)))
    sharedBound =
      SharedUpper.sharedAcceptanceFormulaNodeCountUpper
        (QCircuit.quotientCircuit
          (closedQuotient closed)
          (Closed.closedStateTruth closed))

------------------------------------------------------------------------
-- Actual Cook-authority budget, not merely quotient graph/table budget.
------------------------------------------------------------------------

record ClosedAuthorityFitsBudget
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root)
    (budget : Nat) : Set where
  constructor closed-authority-fits-budget
  field
    authorityFits :
      Size.formulaNodeCount
        (Authority.closedQuotientSATAuthority closed)
      ≤ budget

open ClosedAuthorityFitsBudget public

sharedUpperBoundFitsImpliesAuthorityFits :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  SharedUpper.sharedAcceptanceUpperBound
      (suc rootVariables
        * Quotient.stateCount
            (closedQuotient closed))
    ≤ budget →
  ClosedAuthorityFitsBudget
    closed
    budget
sharedUpperBoundFitsImpliesAuthorityFits
    closed
    sharedFits =
  closed-authority-fits-budget
    (transitive
      (closedAuthorityNodeCountUpper closed)
      sharedFits)
  where
    transitive :
      ∀ {left middle right : Nat} →
      left ≤ middle →
      middle ≤ right →
      left ≤ right
    transitive left≤middle middle≤right =
      Data.Nat.Properties.≤-trans
        left≤middle
        middle≤right

------------------------------------------------------------------------
-- Research consequence.
--
-- Resource closure is now attached to the ACTUAL ordinary Cook authority:
--
--   quotient states s
--       ->
--   exact quotient circuit gates = (n+1)*s
--       ->
--   literal shared SAT authority
--       ->
--   explicit formula-node upper bound.
--
-- The remaining hard theorem is upstream: construct the closed quotient and
-- its structural representative chains from self-instantiation data with
-- stateCount/construction cost small enough that this bound fits the fixed
-- point's own formula budget.
------------------------------------------------------------------------
