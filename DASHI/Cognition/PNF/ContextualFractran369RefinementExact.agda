module DASHI.Cognition.PNF.ContextualFractran369RefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Foundations.Base369BinaryTernaryRefinement as Refinement

------------------------------------------------------------------------
-- Semantic consumers may independently request a binary refinement and a
-- ternary refinement of the same coarse C3 phase observation.  Reuse the repo's
-- exact 2^a 3^b lattice; do not encode both distinctions into one invented trit.
------------------------------------------------------------------------

data SemanticRefinementNeed : Set where
  coarsePhaseOnly : SemanticRefinementNeed
  binarySelectionNeeded : SemanticRefinementNeed
  ternaryDepthNeeded : SemanticRefinementNeed
  binaryAndTernaryNeeded : SemanticRefinementNeed

semanticResolution : SemanticRefinementNeed → Refinement.Resolution23
semanticResolution coarsePhaseOnly = Refinement.phase3Resolution
semanticResolution binarySelectionNeeded = Refinement.phase6Resolution
semanticResolution ternaryDepthNeeded = Refinement.phase9Resolution
semanticResolution binaryAndTernaryNeeded = Refinement.phase18Resolution

binaryAndTernaryRoutesCommute :
  Refinement.binaryRefine
    (Refinement.ternaryRefine Refinement.phase3Resolution)
  ≡ Refinement.ternaryRefine
      (Refinement.binaryRefine Refinement.phase3Resolution)
binaryAndTernaryRoutesCommute =
  Refinement.binary-ternary-refinement-commutes Refinement.phase3Resolution

record ContextualRefinementBoundary : Set where
  constructor contextualRefinementBoundary
  field
    C6AndC9AreIndependentRefinementAxes : Bool
    C18IsCommonRefinement : Bool
    sixPermutationCarrierAutomaticallyEqualsC6 : Bool
    nineRelationSheetAutomaticallyEqualsC9 : Bool

canonicalContextualRefinementBoundary : ContextualRefinementBoundary
canonicalContextualRefinementBoundary =
  contextualRefinementBoundary true true false false
