module DASHI.Physics.Motors.Circuit36927SearchBridgeExact where

------------------------------------------------------------------------
-- Generic circuit topology route search and 3/9/27 phase hierarchy.
-- Relies on existing A* plateau and phase tower abstractions.
--
-- A* searches admissible graph paths, measurement point candidates,
-- and potential connectivity. A* alone NEVER proves KCL/KVL,
-- electromagnetic dynamics, inductive recovery or energy gain.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Circuit
import DASHI.Computation.AStarPlateauFibreExact as AStar
import DASHI.Foundations.Base369TriadicPhaseTower as Tower
import DASHI.Foundations.Base369CirclePhase as Circle
import Base369 as B

open Circuit using (Endpoint; WiringGraph; Route; here; step)

record SearchProblem : Set₁ where
  constructor searchProblem
  field
    graph : WiringGraph
    start target : Endpoint
    edgeCost : ∀ {x y} → WiringGraph.Edge graph x y → Nat
    heuristic : Endpoint → Nat
    trueRemainingCost : Endpoint → Nat

    -- Genuine admissibility and cost-order evidence must come from
    -- a selected model; fields of type Set are not automatically proved.
    BoundedBy : Nat → Nat → Set
    heuristicAdmissible :
      (n : Endpoint) → BoundedBy (heuristic n) (trueRemainingCost n)
    targetCostZero : trueRemainingCost target ≡ zero
    allEdgeCostsNonnegative : Bool

-- A successful path search requires a route witness and a claim that
-- its reported value represents the chosen cost accumulation.
-- In particular a route existing does not entail it is shortest.
record SearchResult (s : SearchProblem) : Set₁ where
  constructor searchResult
  open SearchProblem s
  field
    path : Route graph start target
    reportedCost : Nat
    exactPathCostEvidence : Set

-- To promote a candidate path to optimal, we require an
-- independently justified lower bound for EVERY rival path. This is
-- not derivable merely from an A* tie-order fibre.
record OptimalSearchResult (s : SearchProblem) : Set₁ where
  constructor optimalSearchResult
  open SearchProblem s
  field
    candidate : SearchResult s
    betterOrEqualThan :
      (rival : Route graph start target) → Set
    allRivalCostsCovered :
      (rival : Route graph start target) →
      betterOrEqualThan rival

-- Existing A* module exposes the intended plateau boundary.
-- It is reused by type, without asserting any particular physical
-- circuit satisfies its heuristic-correctness contract.
record ExistingAStarInterface : Set where
  constructor existingAStarInterface
  field
    algorithmBoundary : AStar.AStarFibreBoundary
    modelContract : AStar.AStarCorrectnessContract

-- Do not populate the A* correctness contract with ungrounded Booleans.
-- The bridge exposes the original contract and requires a selected
-- implementation to supply its heuristic and correctness evidence.

record PhaseSearchHierarchy : Set where
  constructor phaseSearchHierarchy
  field
    three : B.TriTruth
    nine : B.NonaryTruth
    twentySeven : Tower.Phase27
    nineMatchesThree : Tower.nonaryToTriSector nine ≡ three
    twentySevenMatchesNine :
      Tower.phase27ToNonarySector twentySeven ≡ nine

-- A canonical hierarchy is available from the proved tower sections.
canonicalPhaseSearchHierarchy :
  (phase : B.TriTruth) → PhaseSearchHierarchy
canonicalPhaseSearchHierarchy phase =
  phaseSearchHierarchy
    phase
    (Circle.triToNonary phase)
    (Tower.triTo27 phase)
    (Tower.triToNonary-section phase)
    (Tower.nonaryTo27-section (Tower.triToNonary phase))

-- Coarse phase is preserved by the selected canonical embedding.
-- This is a phase-index invariant, NOT a route-lifting theorem:
-- edges on a coarse graph may fail to exist on its finer carrier.
