module DASHI.Computation.PathfindingStableCarrierIdentityExact where

-- Stable algebraic identities for the pathfinding fibre family.
--
-- Numerical cardinalities are only shadows of named algorithmic carriers.
-- Equal cardinality never identifies two algorithm roles, nor does it identify
-- a pathfinding carrier with a Base369 phase/refinement carrier.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Generic explicit carrier equivalence.
------------------------------------------------------------------------

record CarrierIso (A B : Set) : Set where
  constructor carrierIso
  field
    to : A → B
    from : B → A
    fromTo : (a : A) → from (to a) ≡ a
    toFrom : (b : B) → to (from b) ≡ b

open CarrierIso public

------------------------------------------------------------------------
-- 2. Stable algorithmic carrier identities.
------------------------------------------------------------------------

-- BFS: two same-layer queue presentations.  This is not a generic Bit2 and is
-- not the Base369 binary-orientation carrier.
data BFSWithinLayerOrder2 : Set where
  bfsLeftThenRight bfsRightThenLeft : BFSWithinLayerOrder2

-- Dijkstra: two tie representatives for equal current minimum key.
data DijkstraEqualMinTie2 : Set where
  dijkstraFirstA dijkstraFirstB : DijkstraEqualMinTie2

-- A*: two representatives in one equal-f plateau.
data AStarEqualFPlateau2 : Set where
  aStarPlateauAFirst aStarPlateauBFirst : AStarEqualFPlateau2

-- Bellman-Ford: two schedules in a finite commuting/confluent regression.
data BellmanFordSchedule2 : Set where
  bellmanFordScheduleAB bellmanFordScheduleBA : BellmanFordSchedule2

-- Bidirectional search carries two independent frontier-tail choices.
record BidirectionalTailPair : Set where
  constructor bidirectionalTailPair
  field
    forwardTailChoice : BFSWithinLayerOrder2
    reverseTailChoice : BFSWithinLayerOrder2

open BidirectionalTailPair public

-- Three abstract observation roles that occur in a tiny frontier consumer.
-- The names are algorithmic, not phase labels.
data FrontierObservation3 : Set where
  frontierNegative frontierNeutral frontierPositive : FrontierObservation3

-- A six-state pathfinding chart: one ternary consumer coordinate and one
-- binary residual coordinate.  The product is literal; no cyclic C6 action is
-- inferred.
record FrontierObservationResidual6 : Set where
  constructor frontierObservationResidual6
  field
    visible : FrontierObservation3
    residual : BFSWithinLayerOrder2

open FrontierObservationResidual6 public

------------------------------------------------------------------------
-- 3. Explicit structural equivalences where intended.
------------------------------------------------------------------------

record FrontierPairCode : Set where
  constructor frontierPairCode
  field
    observationCoordinate : FrontierObservation3
    residualCoordinate : BFSWithinLayerOrder2

open FrontierPairCode public

sixToPair : FrontierObservationResidual6 → FrontierPairCode
sixToPair (frontierObservationResidual6 observation residual) =
  frontierPairCode observation residual

pairToSix : FrontierPairCode → FrontierObservationResidual6
pairToSix (frontierPairCode observation residual) =
  frontierObservationResidual6 observation residual

sixPairFromTo :
  (x : FrontierObservationResidual6) → pairToSix (sixToPair x) ≡ x
sixPairFromTo (frontierObservationResidual6 observation residual) = refl

sixPairToFrom :
  (x : FrontierPairCode) → sixToPair (pairToSix x) ≡ x
sixPairToFrom (frontierPairCode observation residual) = refl

frontierSixIsThreeByTwo :
  CarrierIso FrontierObservationResidual6 FrontierPairCode
frontierSixIsThreeByTwo =
  carrierIso sixToPair pairToSix sixPairFromTo sixPairToFrom

------------------------------------------------------------------------
-- 4. Identity firewalls.
------------------------------------------------------------------------

data BFSTieEqualsDijkstraTie : Set where
data DijkstraTieEqualsAStarPlateau : Set where
data PathfindingSixEqualsCyclicC6 : Set where
data FrontierThreeEqualsBase369C3 : Set where
data EqualCardinalityCreatesAlgorithmicIdentity : Set where

bfsTieNotDijkstraTieByCardinality : BFSTieEqualsDijkstraTie → ⊥
bfsTieNotDijkstraTieByCardinality ()

dijkstraTieNotAStarPlateauByCardinality : DijkstraTieEqualsAStarPlateau → ⊥
dijkstraTieNotAStarPlateauByCardinality ()

pathfindingSixNotCyclicC6WithoutIntertwiner : PathfindingSixEqualsCyclicC6 → ⊥
pathfindingSixNotCyclicC6WithoutIntertwiner ()

frontierThreeNotBase369C3WithoutIntertwiner : FrontierThreeEqualsBase369C3 → ⊥
frontierThreeNotBase369C3WithoutIntertwiner ()

equalCardinalityDoesNotCreateAlgorithmicIdentity :
  EqualCardinalityCreatesAlgorithmicIdentity → ⊥
equalCardinalityDoesNotCreateAlgorithmicIdentity ()

record PathfindingStableCarrierBoundary : Set where
  constructor pathfindingStableCarrierBoundary
  field
    bfsResidualHasNamedCarrier : Bool
    dijkstraResidualHasNamedCarrier : Bool
    bellmanFordResidualHasNamedCarrier : Bool
    aStarResidualHasNamedCarrier : Bool
    bidirectionalResidualHasNamedCarrier : Bool
    sixStateChartIsExplicitThreeByTwoProduct : Bool
    equalCardinalityCreatesIdentity : Bool
    pathfindingSixAutomaticallyCyclicC6 : Bool

canonicalPathfindingStableCarrierBoundary : PathfindingStableCarrierBoundary
canonicalPathfindingStableCarrierBoundary =
  pathfindingStableCarrierBoundary
    true true true true true true false false
