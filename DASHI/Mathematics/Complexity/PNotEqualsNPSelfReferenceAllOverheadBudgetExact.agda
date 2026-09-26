module DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact where

------------------------------------------------------------------------
-- Q1 RESOURCE CURRENCY WITH ALL SELF-REFERENCE OVERHEAD EXPLICIT
--
-- The closed quotient stack already proves
--
--   |authority(root)| <= SharedUpper((n+1) * stateCount).
--
-- For bounded self-reference that inequality is not yet the right currency:
-- quotation, specialization/rebinding, and any other fixed compiler payload
-- must be paid BEFORE the recursive call.
--
-- This owner therefore makes the required inequality literal:
--
--   SharedUpper((n+1) * stateCount)
--     + quotationOverhead
--     + rebindingOverhead
--     <
--   |root|.
--
-- The theorem below compiles that stronger premise to
--
--   |authority(root)| + quotationOverhead + rebindingOverhead < |root|.
--
-- No claim is made that the premise can be inhabited for the self-diagonal
-- family.  Constructing such an inhabitant is the Q1 mathematical wall.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientSATAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedRestrictionQuotientAuthoritySizeExact as AuthoritySize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedUpperBoundExact as SharedUpper

------------------------------------------------------------------------
-- Explicit compiler overhead.
------------------------------------------------------------------------

record SelfReferenceOverhead : Set where
  constructor self-reference-overhead
  field
    quotationOverhead : Nat
    rebindingOverhead : Nat

open SelfReferenceOverhead public

totalOverhead : SelfReferenceOverhead → Nat
totalOverhead overhead =
  quotationOverhead overhead
  + rebindingOverhead overhead

------------------------------------------------------------------------
-- The exact Q1 budget premise.
------------------------------------------------------------------------

record ClosedQuotientAllOverheadFits
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : Closed.ClosedStrictRepresentativeQuotient root)
    (overhead : SelfReferenceOverhead) : Set where
  constructor closed-quotient-all-overhead-fits
  field
    allOverheadStrict :
      (SharedUpper.sharedAcceptanceUpperBound
        (suc rootVariables
          * Quotient.stateCount
              (AuthoritySize.closedQuotient closed))
       + totalOverhead overhead)
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

open ClosedQuotientAllOverheadFits public

------------------------------------------------------------------------
-- The actual recursive payload is strictly smaller after ALL overhead.
------------------------------------------------------------------------

closedAuthorityPlusOverheadUpper :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : Closed.ClosedStrictRepresentativeQuotient root)
    (overhead : SelfReferenceOverhead) →
  Size.formulaNodeCount
      (Authority.closedQuotientSATAuthority closed)
    + totalOverhead overhead
  ≤
  SharedUpper.sharedAcceptanceUpperBound
      (suc rootVariables
        * Quotient.stateCount
            (AuthoritySize.closedQuotient closed))
    + totalOverhead overhead
closedAuthorityPlusOverheadUpper closed overhead =
  NatP.+-mono-≤
    (AuthoritySize.closedAuthorityNodeCountUpper closed)
    NatP.≤-refl

closedAuthorityPlusAllOverheadStrictlySmaller :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : Closed.ClosedStrictRepresentativeQuotient root)
    (overhead : SelfReferenceOverhead) →
  ClosedQuotientAllOverheadFits closed overhead →
  Size.formulaNodeCount
      (Authority.closedQuotientSATAuthority closed)
    + totalOverhead overhead
  <
  Size.formulaNodeCount
      (Bridge.indexedToCook root)
closedAuthorityPlusAllOverheadStrictlySmaller
    closed
    overhead
    budget =
  NatP.≤-<-trans
    (closedAuthorityPlusOverheadUpper closed overhead)
    (allOverheadStrict budget)

------------------------------------------------------------------------
-- Q1 output package.
--
-- The semantic equivalence is already carried by the closed authority owner.
-- This record adds exactly the stronger resource fact needed by the recursive
-- fixed-point layer: the authority remains smaller after compiler overhead.
------------------------------------------------------------------------

record AllOverheadStrictAuthorityDescent
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : Closed.ClosedStrictRepresentativeQuotient root)
    (overhead : SelfReferenceOverhead) : Set₁ where
  constructor all-overhead-strict-authority-descent
  field
    rootToAuthority :
      SAT.Satisfying root →
      Cook.Satisfiable
        (Authority.closedQuotientSATAuthority closed)

    authorityToRoot :
      Cook.Satisfiable
        (Authority.closedQuotientSATAuthority closed) →
      SAT.Satisfying root

    payloadStrictlySmaller :
      Size.formulaNodeCount
          (Authority.closedQuotientSATAuthority closed)
        + totalOverhead overhead
      <
      Size.formulaNodeCount
          (Bridge.indexedToCook root)

open AllOverheadStrictAuthorityDescent public

allOverheadBudgetBuildsStrictAuthorityDescent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : Closed.ClosedStrictRepresentativeQuotient root)
    (overhead : SelfReferenceOverhead) →
  ClosedQuotientAllOverheadFits closed overhead →
  AllOverheadStrictAuthorityDescent closed overhead
allOverheadBudgetBuildsStrictAuthorityDescent
    {root = root}
    closed
    overhead
    budget =
  all-overhead-strict-authority-descent
    (Authority.rootSatisfiableGivesClosedAuthoritySatisfiable closed)
    (Authority.closedAuthoritySatisfiableGivesRootSatisfying closed)
    (closedAuthorityPlusAllOverheadStrictlySmaller
      closed overhead budget)

------------------------------------------------------------------------
-- Research boundary.
--
-- This owner deliberately does NOT derive the allOverheadStrict premise.
-- That premise is now the exact quantitative Q1 target.  In particular, a
-- quotient that beats the raw root size but loses after quotation/rebinding
-- overhead does not count as resource closure.
------------------------------------------------------------------------
