module DASHI.Mathematics.Complexity.PNotEqualsNPClosedQuotientAuthorityDescentExact where

------------------------------------------------------------------------
-- STRICT CLOSED AUTHORITY -> STRUCTURAL REPRESENTATIVE CHAIN
--
-- Canonical quantitative owner:
--
--   PNotEqualsNPClosedAuthorityStrictDescentExact
--
-- already packages the exact downstream resource statement:
--
--   root
--     ≃SAT
--   closedQuotientSATAuthority(root)
--
-- together with strict Cook node-count descent.
--
-- This owner contributes only the next genuinely distinct theorem:
--
-- a StructuralRepresentativeChain for the smaller authority lifts by one
-- semantic descent step to a chain for the root.
--
-- Thus repeated strict closed-authority compression is exactly a well-founded
-- structural-chain construction; no duplicate size/equivalence surface is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_<_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedAuthorityStrictDescentExact as Descent
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientAuthoritySizeExact as AuthoritySize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedUpperBoundExact as SharedUpper
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- One strict semantic descent lifts an existing chain.
------------------------------------------------------------------------

closedAuthorityDescentStep :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Descent.ClosedAuthorityStrictDescent closed →
  Closed.StructuralRepresentativeChain
    (Authority.closedQuotientSATAuthority closed) →
  Closed.StructuralRepresentativeChain
    (Bridge.indexedToCook root)
closedAuthorityDescentStep
    closed
    strictDescent
    authorityChain =
  Closed.descend
    (Descent.equivalent strictDescent)
    (Descent.strictlySmaller strictDescent)
    authorityChain

------------------------------------------------------------------------
-- The literal shared-compiler budget inequality supplies that descent package.
------------------------------------------------------------------------

sharedUpperStrictlyBelowRootImpliesAuthorityChain :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  SharedUpper.sharedAcceptanceUpperBound
      (suc rootVariables
        * Quotient.stateCount
            (AuthoritySize.closedQuotient closed))
    <
  DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact.formulaNodeCount
      (Bridge.indexedToCook root) →
  Closed.StructuralRepresentativeChain
    (Authority.closedQuotientSATAuthority closed) →
  Closed.StructuralRepresentativeChain
    (Bridge.indexedToCook root)
sharedUpperStrictlyBelowRootImpliesAuthorityChain
    closed
    strictBudget
    authorityChain =
  closedAuthorityDescentStep
    closed
    (Descent.strictBudgetBuildsClosedAuthorityStrictDescent
      closed
      strictBudget)
    authorityChain

------------------------------------------------------------------------
-- Research consequence.
--
-- The canonical recursive resource condition is now:
--
--   construct closed quotient for root
--   + prove its shared authority upper bound is < |root|
--   + recursively close the smaller authority
--       ->
--   structurally close root.
--
-- The global structural-chain firewall prevents promoting this into a generic
-- SAT recursion theorem.  The missing constructor must stay scoped to the
-- special self-instantiation lineage and must itself fit the bounded fixed
-- point budget.
------------------------------------------------------------------------
