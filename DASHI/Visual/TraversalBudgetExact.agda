module DASHI.Visual.TraversalBudgetExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BOUNDED SEMANTIC EXPANSION
--
-- Depth bounds do not control fan-out. Every focused traversal therefore also
-- carries explicit node and edge budgets. Reaching a budget truncates the
-- presentation; it never changes the authority graph.
------------------------------------------------------------------------

record TraversalBudget : Set where
  constructor traversalBudget
  field
    maxTraversalNodes : Nat
    maxTraversalEdges : Nat

open TraversalBudget public

canonicalTraversalBudget : TraversalBudget
canonicalTraversalBudget =
  traversalBudget 250 800

data TraversalCompletion : Set where
  traversalComplete : TraversalCompletion
  traversalTruncated : TraversalCompletion

record TraversalReceipt : Set where
  constructor traversalReceipt
  field
    traversalCompletion : TraversalCompletion
    emittedNodeCount : Nat
    emittedEdgeCount : Nat
    omittedNodeCount : Nat
    omittedEdgeCount : Nat

open TraversalReceipt public

record TraversalBudgetBoundary : Set where
  constructor traversalBudgetBoundary
  field
    depthBoundAloneIsResourceBound : Bool
    depthBoundAloneIsResourceBoundIsFalse :
      depthBoundAloneIsResourceBound ≡ false

    truncationMayDeleteAuthorityGraphEvidence : Bool
    truncationMayDeleteAuthorityGraphEvidenceIsFalse :
      truncationMayDeleteAuthorityGraphEvidence ≡ false

    traversalBudgetMayInventSemanticEdges : Bool
    traversalBudgetMayInventSemanticEdgesIsFalse :
      traversalBudgetMayInventSemanticEdges ≡ false

canonicalTraversalBudgetBoundary : TraversalBudgetBoundary
canonicalTraversalBudgetBoundary =
  traversalBudgetBoundary
    false refl
    false refl
    false refl
