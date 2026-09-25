module DASHI.Mathematics.Complexity.PNotEqualsNPClosedAuthorityStrictDescentExact where

------------------------------------------------------------------------
-- CLOSED QUOTIENT AUTHORITY -> STRICT COOK-LEVEL SEMANTIC DESCENT
--
-- Existing results already give:
--
--   1. exact SAT equivalence between the indexed root and the closed quotient
--      authority formula;
--
--   2. an explicit upper bound on the authority's ordinary Cook node count.
--
-- This owner composes them with one strict budget inequality:
--
--   sharedAcceptanceUpperBound ((n + 1) * stateCount)
--      <
--   nodeCount(root).
--
-- The consequence is a literal ordinary Cook formula which is:
--
--   * equisatisfiable with the root; and
--   * strictly smaller than the root.
--
-- No call to the hypothetical polynomial SAT decider occurs in the
-- construction or proof.
--
-- This is the exact downstream object a bounded fixed-point construction needs
-- from P9: not merely a small quotient graph, but a strict semantic descent on
-- the Clay-critical Cook carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientAuthoritySizeExact as AuthoritySize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedUpperBoundExact as SharedUpper

------------------------------------------------------------------------
-- The literal smaller formula.
------------------------------------------------------------------------

closedAuthorityFormula :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Closed.ClosedStrictRepresentativeQuotient root →
  Cook.BooleanFormula
closedAuthorityFormula =
  Authority.closedQuotientSATAuthority

------------------------------------------------------------------------
-- Exact Cook-level semantic equivalence.
------------------------------------------------------------------------

closedAuthorityEquivalentToRoot :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook root)
    (closedAuthorityFormula closed)
closedAuthorityEquivalentToRoot closed =
  Authority.cookRootSatisfiableGivesClosedAuthoritySatisfiable closed
  ,
  Authority.closedAuthoritySatisfiableGivesCookRootSatisfiable closed

------------------------------------------------------------------------
-- Quantitative strict descent.
------------------------------------------------------------------------

closedAuthorityStrictlySmallerFromSharedUpper :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  SharedUpper.sharedAcceptanceUpperBound
      (suc rootVariables
        * Quotient.stateCount
            (AuthoritySize.closedQuotient closed))
    <
    Size.formulaNodeCount
      (Bridge.indexedToCook root) →
  Size.formulaNodeCount
      (closedAuthorityFormula closed)
    <
  Size.formulaNodeCount
      (Bridge.indexedToCook root)
closedAuthorityStrictlySmallerFromSharedUpper
    closed
    strictBudget =
  NatP.≤-<-trans
    (AuthoritySize.closedAuthorityNodeCountUpper closed)
    strictBudget

------------------------------------------------------------------------
-- Single package consumed by the next bounded-fixed-point seam.
------------------------------------------------------------------------

record ClosedAuthorityStrictDescent
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) : Set₁ where
  constructor closed-authority-strict-descent
  field
    equivalent :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook root)
        (closedAuthorityFormula closed)

    strictlySmaller :
      Size.formulaNodeCount
        (closedAuthorityFormula closed)
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

open ClosedAuthorityStrictDescent public

strictBudgetBuildsClosedAuthorityStrictDescent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  SharedUpper.sharedAcceptanceUpperBound
      (suc rootVariables
        * Quotient.stateCount
            (AuthoritySize.closedQuotient closed))
    <
    Size.formulaNodeCount
      (Bridge.indexedToCook root) →
  ClosedAuthorityStrictDescent closed
strictBudgetBuildsClosedAuthorityStrictDescent
    closed
    strictBudget =
  closed-authority-strict-descent
    (closedAuthorityEquivalentToRoot closed)
    (closedAuthorityStrictlySmallerFromSharedUpper
      closed
      strictBudget)

------------------------------------------------------------------------
-- Research consequence.
--
-- P9's downstream resource currency is now exact:
--
--   closed quotient
--      +
--   shared authority upper bound < root node count
--      ->
--   strictly smaller equisatisfiable ordinary Cook formula.
--
-- So the next genuinely open theorem is no longer "show the quotient is
-- finite" or even "show the authority has some polynomial bound".  It must
-- construct the closed quotient from the special self-instantiation data with
-- a state bound strong enough to make the strict inequality above hold.
--
-- Once such an inhabitant exists, the quotient machinery exports an actual
-- strict semantic descent on the same Cook formula lineage used by the Clay
-- SAT lower-bound statement.
------------------------------------------------------------------------
