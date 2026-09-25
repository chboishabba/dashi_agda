module DASHI.Mathematics.Complexity.PNotEqualsNPClosedQuotientAuthorityDescentExact where

------------------------------------------------------------------------
-- CLOSED QUOTIENT AUTHORITY AS A STRICT SEMANTIC DESCENT STEP
--
-- Existing:
--
--   PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact
--     proves exact SAT equivalence between the indexed root (on the Cook
--     carrier) and the structurally closed quotient authority.
--
--   PNotEqualsNPClosedRestrictionQuotientAuthoritySizeExact
--     bounds the literal authority size by the quotient depth/state budget.
--
--   PNotEqualsNPClosedStrictRepresentativeQuotientExact
--     defines StructuralRepresentativeChain:
--
--       formula
--         -> strictly smaller equisatisfiable formula
--         -> ...
--         -> literal Boolean constant.
--
-- This owner composes them.
--
-- If the closed quotient authority is strictly smaller than the root, then a
-- StructuralRepresentativeChain for the authority lifts by ONE exact semantic
-- descent step to a chain for the root.
--
-- Thus the quantitative condition
--
--   |authority(root)| < |root|
--
-- is exactly the recursive resource-closure condition, not merely a heuristic
-- compression score.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientAuthoritySizeExact as AuthoritySize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedUpperBoundExact as SharedUpper
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- Exact Cook-level SAT equivalence supplied by the closed authority.
------------------------------------------------------------------------

closedAuthorityEquivalentToRoot :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Closed.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook root)
    (Authority.closedQuotientSATAuthority closed)
closedAuthorityEquivalentToRoot
    closed =
  Authority.cookRootSatisfiableGivesClosedAuthoritySatisfiable
    closed
  ,
  Authority.closedAuthoritySatisfiableGivesCookRootSatisfiable
    closed

------------------------------------------------------------------------
-- One strict authority descent step.
------------------------------------------------------------------------

closedAuthorityDescentStep :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  Size.formulaNodeCount
      (Authority.closedQuotientSATAuthority closed)
    <
  Size.formulaNodeCount
      (Bridge.indexedToCook root) →
  Closed.StructuralRepresentativeChain
    (Authority.closedQuotientSATAuthority closed) →
  Closed.StructuralRepresentativeChain
    (Bridge.indexedToCook root)
closedAuthorityDescentStep
    closed authoritySmaller authorityChain =
  Closed.descend
    (closedAuthorityEquivalentToRoot closed)
    authoritySmaller
    authorityChain

------------------------------------------------------------------------
-- The generic shared-compiler upper bound can pay strictness.
------------------------------------------------------------------------

sharedUpperStrictlyBelowRootImpliesAuthorityDescent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      Closed.ClosedStrictRepresentativeQuotient root) →
  SharedUpper.sharedAcceptanceUpperBound
      (suc rootVariables
        *
        Quotient.stateCount
          (AuthoritySize.closedQuotient closed))
    <
  Size.formulaNodeCount
      (Bridge.indexedToCook root) →
  Closed.StructuralRepresentativeChain
    (Authority.closedQuotientSATAuthority closed) →
  Closed.StructuralRepresentativeChain
    (Bridge.indexedToCook root)
sharedUpperStrictlyBelowRootImpliesAuthorityDescent
    closed sharedUpperBelowRoot authorityChain =
  closedAuthorityDescentStep
    closed
    authorityBelowRoot
    authorityChain
  where
    authorityBelowRoot :
      Size.formulaNodeCount
          (Authority.closedQuotientSATAuthority closed)
      <
      Size.formulaNodeCount
          (Bridge.indexedToCook root)
    authorityBelowRoot =
      NatP.≤-<-trans
        (AuthoritySize.closedAuthorityNodeCountUpper
          closed)
        sharedUpperBelowRoot

------------------------------------------------------------------------
-- Research consequence.
--
-- A structurally closed quotient becomes a genuine well-founded semantic
-- reduction exactly when its compiled authority is smaller than its root.
--
-- Repeated application would terminate by formula-node size IF one can
-- construct an appropriate closed quotient for each generated authority.
--
-- That recursive constructor must remain self-family-specific; the global
-- structural-chain firewall proves that a constructor working for arbitrary
-- formulas is already an exact SAT solver.
------------------------------------------------------------------------
