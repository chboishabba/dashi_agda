module DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact where

------------------------------------------------------------------------
-- STRUCTURALLY CLOSED QUOTIENT -> ORDINARY SAT AUTHORITY, WITH NO D CALLS
--
-- Compose:
--
--   PNotEqualsNPClosedStrictRepresentativeQuotientExact
--   PNotEqualsNPRestrictionQuotientSATAuthorityExact
--
-- The closed strict quotient computes every state label from a literal
-- descending chain ending at constant true/false.  This owner feeds those
-- labels into the exact quotient DP -> circuit -> shared/Tseitin compiler.
--
-- Output:
--
--   closedQuotientSATAuthority : Cook.BooleanFormula
--
-- with exact equivalence:
--
--   SAT(indexed root)
--      iff
--   SAT(closedQuotientSATAuthority).
--
-- No call to the hypothetical polynomial SAT decider D occurs in the authority
-- construction or state labelling.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed

------------------------------------------------------------------------
-- Literal authority formula.
------------------------------------------------------------------------

closedQuotientSATAuthority :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Closed.ClosedStrictRepresentativeQuotient root →
  Cook.BooleanFormula
closedQuotientSATAuthority closed =
  Authority.quotientSATAuthority
    quotient
    (Closed.closedTerminalLabels closed)
  where
    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Strict.quotient
        (Closed.strictQuotient closed)

------------------------------------------------------------------------
-- Indexed root -> authority.
------------------------------------------------------------------------

rootSatisfiableGivesClosedAuthoritySatisfiable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  SAT.Satisfying root →
  Cook.Satisfiable
    (closedQuotientSATAuthority closed)
rootSatisfiableGivesClosedAuthoritySatisfiable
    closed =
  Authority.rootSatisfiableGivesQuotientAuthoritySatisfiable
    quotient
    Closed.finiteSATOracle
    (Closed.closedTerminalLabels closed)
  where
    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Strict.quotient
        (Closed.strictQuotient closed)

------------------------------------------------------------------------
-- Authority -> indexed root.
------------------------------------------------------------------------

closedAuthoritySatisfiableGivesRootSatisfying :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Cook.Satisfiable
    (closedQuotientSATAuthority closed) →
  SAT.Satisfying root
closedAuthoritySatisfiableGivesRootSatisfying
    closed =
  Authority.quotientAuthoritySatisfiableGivesRootSatisfying
    quotient
    Closed.finiteSATOracle
    (Closed.closedTerminalLabels closed)
  where
    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Strict.quotient
        (Closed.strictQuotient closed)

------------------------------------------------------------------------
-- Same equivalence stated entirely on the ordinary Cook carrier.
------------------------------------------------------------------------

cookRootSatisfiableGivesClosedAuthoritySatisfiable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Cook.Satisfiable
    (Bridge.indexedToCook root) →
  Cook.Satisfiable
    (closedQuotientSATAuthority closed)
cookRootSatisfiableGivesClosedAuthoritySatisfiable
    closed
    rootCookSat =
  rootSatisfiableGivesClosedAuthoritySatisfiable
    closed
    (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
      _
      rootCookSat)

closedAuthoritySatisfiableGivesCookRootSatisfiable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Cook.Satisfiable
    (closedQuotientSATAuthority closed) →
  Cook.Satisfiable
    (Bridge.indexedToCook root)
closedAuthoritySatisfiableGivesCookRootSatisfiable
    closed
    authoritySat =
  Bridge.indexedSatisfyingGivesCookSatisfiable
    _
    (closedAuthoritySatisfiableGivesRootSatisfying
      closed
      authoritySat)

------------------------------------------------------------------------
-- Exact package.
------------------------------------------------------------------------

record ClosedQuotientAuthorityExact
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) : Set₁ where
  constructor closed-quotient-authority-exact
  field
    rootToAuthority :
      Cook.Satisfiable
        (Bridge.indexedToCook root) →
      Cook.Satisfiable
        (closedQuotientSATAuthority closed)

    authorityToRoot :
      Cook.Satisfiable
        (closedQuotientSATAuthority closed) →
      Cook.Satisfiable
        (Bridge.indexedToCook root)

open ClosedQuotientAuthorityExact public

closedQuotientAuthorityExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  ClosedQuotientAuthorityExact closed
closedQuotientAuthorityExact closed =
  closed-quotient-authority-exact
    (cookRootSatisfiableGivesClosedAuthoritySatisfiable
      closed)
    (closedAuthoritySatisfiableGivesCookRootSatisfiable
      closed)

------------------------------------------------------------------------
-- Research consequence.
--
-- The downstream route no longer needs D even on smaller representatives:
--
--   structurally closed quotient
--      -> structural constant labels
--      -> exact Shannon DP
--      -> literal circuit
--      -> ordinary Cook SAT authority
--      -> exact root SAT semantics.
--
-- The remaining Clay-critical theorem is therefore upstream and constructive:
-- derive the quotient, strict representatives, and their descending chains from
-- the special self-instantiation program within the self-size budget.
------------------------------------------------------------------------
