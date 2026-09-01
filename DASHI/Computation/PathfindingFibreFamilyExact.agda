module DASHI.Computation.PathfindingFibreFamilyExact where

-- Cross-algorithm pathfinding fibre map.  Each algorithm exposes a different
-- consumer-visible certificate and retains a different residual scheduling or
-- ordering fibre.  Shared cardinality does not imply shared identity or law.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Computation.PathfindingFibreCoreExact as Core
import DASHI.Computation.PathfindingStableCarrierIdentityExact as Stable
import DASHI.Computation.BFSLayerFibreExact as BFS
import DASHI.Computation.DijkstraQueueFibreExact as Dijkstra
import DASHI.Computation.BellmanFordRelaxationScheduleFibreExact as BellmanFord
import DASHI.Computation.AStarPlateauFibreExact as AStar
import DASHI.Computation.BidirectionalMeetingFibreExact as Bidi
import DASHI.Computation.SSSPBMSSPConsumerContractExact as BMSSP

record PathfindingFibreFamily : Set where
  constructor pathfindingFibreFamily
  field
    bfsResidualIsWithinLayerOrder : Bool
    bfsResidualIsWithinLayerOrderIsTrue : bfsResidualIsWithinLayerOrder ≡ true

    dijkstraResidualIsEqualMinimumTieOrder : Bool
    dijkstraResidualIsEqualMinimumTieOrderIsTrue :
      dijkstraResidualIsEqualMinimumTieOrder ≡ true

    bellmanFordScheduleResidualNeedsConfluence : Bool
    bellmanFordScheduleResidualNeedsConfluenceIsTrue :
      bellmanFordScheduleResidualNeedsConfluence ≡ true

    aStarResidualIsEqualFPlateauOrder : Bool
    aStarResidualIsEqualFPlateauOrderIsTrue :
      aStarResidualIsEqualFPlateauOrder ≡ true

    bidirectionalResidualIsTwoFrontierTailOrder : Bool
    bidirectionalResidualIsTwoFrontierTailOrderIsTrue :
      bidirectionalResidualIsTwoFrontierTailOrder ≡ true

    bmsspResidualIsUnexposedPullTail : Bool
    bmsspResidualIsUnexposedPullTailIsTrue :
      bmsspResidualIsUnexposedPullTail ≡ true

    residualCarriersHaveStableAlgorithmicNames : Bool
    residualCarriersHaveStableAlgorithmicNamesIsTrue :
      residualCarriersHaveStableAlgorithmicNames ≡ true

    equalCardinalityIdentifiesResidualRoles : Bool
    equalCardinalityIdentifiesResidualRolesIsFalse :
      equalCardinalityIdentifiesResidualRoles ≡ false

    allAlgorithmsShareIdenticalResidualGroup : Bool
    allAlgorithmsShareIdenticalResidualGroupIsFalse :
      allAlgorithmsShareIdenticalResidualGroup ≡ false

    quotientAloneProvesAlgorithmCorrectness : Bool
    quotientAloneProvesAlgorithmCorrectnessIsFalse :
      quotientAloneProvesAlgorithmCorrectness ≡ false

canonicalPathfindingFibreFamily : PathfindingFibreFamily
canonicalPathfindingFibreFamily =
  pathfindingFibreFamily
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

stableIdentityBoundary : Stable.PathfindingStableCarrierBoundary
stableIdentityBoundary = Stable.canonicalPathfindingStableCarrierBoundary
