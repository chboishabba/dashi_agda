module DASHI.Reasoning.TrialecticT27GraphGrothendieckSheafExact where

------------------------------------------------------------------------
-- GROTHENDIECK DESCENT WITH A POLICY-COMPLETED T^27 GLOBAL GRAPH
--
-- The mature relational site has local edge sections T^9, vertex sections T^3,
-- and a global compatible boundary T^18.  TrialecticT9T18T27GraphExtensionExact
-- proves that, once an explicit completion policy P : T^18 -> T^9 is supplied,
-- the completed graph in ambient T^27 has exactly T^18 free data.
--
-- This file transports the existing triadic sheaf through that exact global
-- carrier equivalence.  Local sections and overlap maps are unchanged:
--
--   vertex = T^3
--   edge   = T^9
--   global = CompletedT27 P  (embedded in ambient T^27)
--
-- The unconstrained ambient T^27 carrier is NOT used as the global sheaf
-- section: only the graph-completed subtype is.  Hence the added nine
-- coordinates are policy-determined rather than fabricated new information.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as Old
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower

------------------------------------------------------------------------
-- 1. Exact equivalence between the old T^18 global section and the completed
--    T^27 graph for any explicitly supplied completion policy.
------------------------------------------------------------------------

boundaryToCompletedT27 :
  (policy : Tower.T27CompletionPolicy) →
  Cell.CompatibleThreeCellTrialecticBoundary →
  Tower.CompletedT27 policy
boundaryToCompletedT27 policy boundary =
  Tower.completed-t27 (Tower.compatibleBoundaryToT18 boundary)

completedT27ToBoundary :
  (policy : Tower.T27CompletionPolicy) →
  Tower.CompletedT27 policy →
  Cell.CompatibleThreeCellTrialecticBoundary
completedT27ToBoundary policy completed =
  Cell.coordinatesToCompatibleBoundary
    (Tower.t18ToStructuredBoundaryCoordinates
      (Tower.freeT18 completed))

boundaryCompletedBoundaryRoundTrip :
  (policy : Tower.T27CompletionPolicy) →
  (boundary : Cell.CompatibleThreeCellTrialecticBoundary) →
  completedT27ToBoundary policy (boundaryToCompletedT27 policy boundary)
  ≡ boundary
boundaryCompletedBoundaryRoundTrip policy boundary =
  trans
    (cong Cell.coordinatesToCompatibleBoundary
      (Tower.structuredBoundaryT18RoundTrip
        (Cell.compatibleBoundaryToCoordinates boundary)))
    (Cell.boundaryCoordinatesRoundTrip boundary)

completedBoundaryCompletedRoundTrip :
  (policy : Tower.T27CompletionPolicy) →
  (completed : Tower.CompletedT27 policy) →
  boundaryToCompletedT27 policy (completedT27ToBoundary policy completed)
  ≡ completed
completedBoundaryCompletedRoundTrip policy (Tower.completed-t27 coordinates) =
  cong Tower.completed-t27
    (trans
      (cong Tower.structuredBoundaryCoordinatesToT18
        (Cell.coordinatesBoundaryRoundTrip
          (Tower.t18ToStructuredBoundaryCoordinates coordinates)))
      (Tower.t18StructuredBoundaryRoundTrip coordinates))

------------------------------------------------------------------------
-- 2. Global restrictions.  Forget only the policy-completed third face and
--    apply the already-owned exact T^18 -> T^9 restrictions.
------------------------------------------------------------------------

restrictCompletedAB :
  (policy : Tower.T27CompletionPolicy) →
  Tower.CompletedT27 policy →
  Cell.CellDialectic
restrictCompletedAB policy completed =
  Cell.edgeAB (completedT27ToBoundary policy completed)

restrictCompletedBC :
  (policy : Tower.T27CompletionPolicy) →
  Tower.CompletedT27 policy →
  Cell.CellDialectic
restrictCompletedBC policy completed =
  Cell.edgeBC (completedT27ToBoundary policy completed)

restrictCompletedCA :
  (policy : Tower.T27CompletionPolicy) →
  Tower.CompletedT27 policy →
  Cell.CellDialectic
restrictCompletedCA policy completed =
  Cell.edgeCA (completedT27ToBoundary policy completed)

------------------------------------------------------------------------
-- 3. Glue the same compatible local T^9 family, then transport the exact old
--    T^18 result into the completed T^27 graph.
------------------------------------------------------------------------

glueCompletedT27 :
  (policy : Tower.T27CompletionPolicy) →
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  RelSheaf.CompatibleOnTriadicCover Old.cellOverlapSystem locals →
  Tower.CompletedT27 policy
glueCompletedT27 policy locals compatibility =
  boundaryToCompletedT27 policy (Old.glueStructured locals compatibility)

glueCompletedRestrictsAB :
  (policy : Tower.T27CompletionPolicy) →
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover Old.cellOverlapSystem locals) →
  restrictCompletedAB policy (glueCompletedT27 policy locals compatibility)
  ≡ RelSheaf.localAB locals
glueCompletedRestrictsAB policy locals compatibility
  rewrite boundaryCompletedBoundaryRoundTrip policy
    (Old.glueStructured locals compatibility) =
  Old.glueStructuredRestrictsAB locals compatibility

glueCompletedRestrictsBC :
  (policy : Tower.T27CompletionPolicy) →
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover Old.cellOverlapSystem locals) →
  restrictCompletedBC policy (glueCompletedT27 policy locals compatibility)
  ≡ RelSheaf.localBC locals
glueCompletedRestrictsBC policy locals compatibility
  rewrite boundaryCompletedBoundaryRoundTrip policy
    (Old.glueStructured locals compatibility) =
  Old.glueStructuredRestrictsBC locals compatibility

glueCompletedRestrictsCA :
  (policy : Tower.T27CompletionPolicy) →
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover Old.cellOverlapSystem locals) →
  restrictCompletedCA policy (glueCompletedT27 policy locals compatibility)
  ≡ RelSheaf.localCA locals
glueCompletedRestrictsCA policy locals compatibility
  rewrite boundaryCompletedBoundaryRoundTrip policy
    (Old.glueStructured locals compatibility) =
  Old.glueStructuredRestrictsCA locals compatibility

completedT27TriadicSheaf :
  (policy : Tower.T27CompletionPolicy) →
  RelSheaf.TriadicRelationalSheaf
    Cell.CellDialectic
    Cell.TrialecticBasis3Cell
    (Tower.CompletedT27 policy)
completedT27TriadicSheaf policy = record
  { RelSheaf.overlaps = Old.cellOverlapSystem
  ; RelSheaf.restrictGlobalAB = restrictCompletedAB policy
  ; RelSheaf.restrictGlobalBC = restrictCompletedBC policy
  ; RelSheaf.restrictGlobalCA = restrictCompletedCA policy
  ; RelSheaf.glue = glueCompletedT27 policy
  ; RelSheaf.glueRestrictsAB = glueCompletedRestrictsAB policy
  ; RelSheaf.glueRestrictsBC = glueCompletedRestrictsBC policy
  ; RelSheaf.glueRestrictsCA = glueCompletedRestrictsCA policy
  }

------------------------------------------------------------------------
-- 4. Exact round trip from a completed global section through its three old
--    local restrictions and old compatibility witness.
------------------------------------------------------------------------

completedStructuredLocals :
  (policy : Tower.T27CompletionPolicy) →
  Tower.CompletedT27 policy →
  RelSheaf.TriadicLocals Cell.CellDialectic
completedStructuredLocals policy completed =
  Old.structuredLocals (completedT27ToBoundary policy completed)

completedStructuredCompatibility :
  (policy : Tower.T27CompletionPolicy) →
  (completed : Tower.CompletedT27 policy) →
  RelSheaf.CompatibleOnTriadicCover
    Old.cellOverlapSystem
    (completedStructuredLocals policy completed)
completedStructuredCompatibility policy completed =
  Old.structuredCompatibility (completedT27ToBoundary policy completed)

completedGlueRoundTrip :
  (policy : Tower.T27CompletionPolicy) →
  (completed : Tower.CompletedT27 policy) →
  RelSheaf.glue (completedT27TriadicSheaf policy)
    (completedStructuredLocals policy completed)
    (completedStructuredCompatibility policy completed)
  ≡ completed
completedGlueRoundTrip policy completed =
  trans
    (cong (boundaryToCompletedT27 policy)
      (Old.structuredGlueRoundTrip
        (completedT27ToBoundary policy completed)))
    (completedBoundaryCompletedRoundTrip policy completed)

------------------------------------------------------------------------
-- 5. Promotion boundary.
------------------------------------------------------------------------

record TrialecticT27GraphGrothendieckSheafBoundary : Set where
  constructor trialectic-t27-graph-grothendieck-sheaf-boundary
  field
    globalT18ReplacedByCompletedT27Graph : Bool
    edgeSectionsRemainT9 : Bool
    vertexSectionsRemainT3 : Bool
    completedT27GlobalIsomorphicToT18 : Bool
    triadicSheafDescentTransportedToCompletedT27 : Bool
    completedGlobalGlueRoundTripPaid : Bool
    unconstrainedAmbientT27UsedAsGlobalSection : Bool
    completionPolicyManufacturedByGrothendieckDescent : Bool

open TrialecticT27GraphGrothendieckSheafBoundary public

canonicalTrialecticT27GraphGrothendieckSheafBoundary :
  TrialecticT27GraphGrothendieckSheafBoundary
canonicalTrialecticT27GraphGrothendieckSheafBoundary =
  trialectic-t27-graph-grothendieck-sheaf-boundary
    true true true true true true false false
