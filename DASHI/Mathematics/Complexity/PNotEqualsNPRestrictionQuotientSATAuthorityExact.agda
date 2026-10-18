module DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientSATAuthorityExact where

------------------------------------------------------------------------
-- FINITE RESTRICTION QUOTIENT -> ORDINARY SAT AUTHORITY
--
-- Compose:
--
--   restriction quotient
--      -> exact depth/state Shannon DP
--      -> literal zero-input quotient circuit
--      -> exact circuit semantics
--      -> shared/Tseitin SAT formula.
--
-- Main result:
--
--   sharedAcceptanceFormula(quotientCircuit)
--
-- is satisfiable iff the exact SAT oracle accepts the ORIGINAL indexed root.
--
-- Thus a resource-closing quotient is now an ordinary Cook BooleanFormula
-- authority with no remaining circuit/representation semantic gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (Vec; [])
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientCircuitExact as QCircuit
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientCircuitSemanticsExact as CircuitSemantics
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Shared

------------------------------------------------------------------------
-- Literal authority formula.
------------------------------------------------------------------------

quotientSATAuthority :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle) →
  Cook.BooleanFormula
quotientSATAuthority quotient labels =
  Shared.sharedAcceptanceFormula
    (QCircuit.quotientCircuit
      quotient
      (DP.terminalTruth labels))

------------------------------------------------------------------------
-- Root truth -> authority satisfiable.
------------------------------------------------------------------------

rootAcceptedGivesQuotientAuthoritySatisfiable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) →
  Search.decide oracle root ≡ true →
  Cook.Satisfiable
    (quotientSATAuthority quotient labels)
rootAcceptedGivesQuotientAuthoritySatisfiable
    quotient
    oracle
    labels
    rootAccepted =
  Shared.acceptedInputGivesSharedSatisfiable
    circuit
    []
    circuitAccepted
  where
    circuit :
      Circuit.ConcreteBooleanCircuit zero
    circuit =
      QCircuit.quotientCircuit
        quotient
        (DP.terminalTruth labels)

    circuitAccepted :
      Circuit.evaluateCircuit circuit []
      ≡ true
    circuitAccepted =
      trans
        (CircuitSemantics.quotientCircuitComputesRootDecision
          quotient
          oracle
          labels)
        rootAccepted

------------------------------------------------------------------------
-- Authority satisfiable -> root truth.
------------------------------------------------------------------------

quotientAuthoritySatisfiableGivesRootAccepted :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) →
  Cook.Satisfiable
    (quotientSATAuthority quotient labels) →
  Search.decide oracle root ≡ true
quotientAuthoritySatisfiableGivesRootAccepted
    quotient
    oracle
    labels
    authoritySat
    with
      Shared.sharedSatisfiableGivesAcceptedInput
        circuit
        authoritySat
... | [] , circuitAccepted =
  trans
    (sym
      (CircuitSemantics.quotientCircuitComputesRootDecision
        quotient
        oracle
        labels))
    circuitAccepted
  where
    circuit :
      Circuit.ConcreteBooleanCircuit zero
    circuit =
      QCircuit.quotientCircuit
        quotient
        (DP.terminalTruth labels)

------------------------------------------------------------------------
-- Exact authority equivalence at the oracle-decision level.
------------------------------------------------------------------------

record QuotientSATAuthorityExact
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) : Set₁ where
  constructor quotient-sat-authority-exact
  field
    rootToAuthority :
      Search.decide oracle root ≡ true →
      Cook.Satisfiable
        (quotientSATAuthority quotient labels)

    authorityToRoot :
      Cook.Satisfiable
        (quotientSATAuthority quotient labels) →
      Search.decide oracle root ≡ true

open QuotientSATAuthorityExact public

quotientSATAuthorityExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) →
  QuotientSATAuthorityExact
    quotient
    oracle
    labels
quotientSATAuthorityExact
    quotient
    oracle
    labels =
  quotient-sat-authority-exact
    (rootAcceptedGivesQuotientAuthoritySatisfiable
      quotient
      oracle
      labels)
    (quotientAuthoritySatisfiableGivesRootAccepted
      quotient
      oracle
      labels)

------------------------------------------------------------------------
-- Exact SAT-equivalence with the indexed root itself.
------------------------------------------------------------------------

rootSatisfiableGivesQuotientAuthoritySatisfiable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) →
  SAT.Satisfying root →
  Cook.Satisfiable
    (quotientSATAuthority quotient labels)
rootSatisfiableGivesQuotientAuthoritySatisfiable
    quotient
    oracle
    labels
    rootSat =
  rootAcceptedGivesQuotientAuthoritySatisfiable
    quotient
    oracle
    labels
    (Search.complete oracle root rootSat)

quotientAuthoritySatisfiableGivesRootSatisfying :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : DP.TerminalStateLabelling quotient oracle) →
  Cook.Satisfiable
    (quotientSATAuthority quotient labels) →
  SAT.Satisfying root
quotientAuthoritySatisfiableGivesRootSatisfying
    quotient
    oracle
    labels
    authoritySat =
  Search.sound
    oracle
    root
    (quotientAuthoritySatisfiableGivesRootAccepted
      quotient
      oracle
      labels
      authoritySat)

------------------------------------------------------------------------
-- Research consequence.
--
-- Downstream representation is now closed:
--
--   finite semantic quotient
--      -> exact DP
--      -> exact circuit
--      -> ordinary SAT formula
--      -> exact root SAT semantics.
--
-- The open theorem is no longer a compiler theorem.  It is the new
-- mathematics required to CONSTRUCT, from the special self-instantiation
-- structure and without target SAT calls:
--
--   * a useful quotient/order;
--   * strict representatives / terminal authority;
--   * a resource budget small enough to close the bounded fixed point.
------------------------------------------------------------------------
