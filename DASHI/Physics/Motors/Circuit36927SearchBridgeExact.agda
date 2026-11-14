module DASHI.Physics.Motors.Circuit36927SearchBridgeExact where

------------------------------------------------------------------------
-- Generic circuit topology route search and 3/9/27 phase hierarchy.
-- Relies on existing A* plateau and phase tower abstractions.
--
-- A* searches admissible graph paths, measurement point candidates,
-- and potential connectivity. A* alone NEVER proves KCL/KVL,
-- electromagnetic dynamics, inductive recovery or energy gain.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Circuit
import DASHI.Computation.AStarPlateauFibreExact as AStar
import DASHI.Foundations.Base369TriadicPhaseTower as Tower
import DASHI.Foundations.Base369CirclePhase as Circle
import Base369 as B

open Circuit using (Endpoint; WiringGraph; Route; here; step)

-- Constructive numeric ordering: there is no arbitrary user-defined
-- relation that could make an invalid optimality receipt vacuous.
data _≤_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ n
  suc≤ : ∀ {m n} → m ≤ n → suc m ≤ suc n

record SearchProblem : Set₁ where
  constructor searchProblem
  field
    graph : WiringGraph
    start target : Endpoint
    edgeCost : ∀ {x y} → WiringGraph.Edge graph x y → Nat
    heuristic : Endpoint → Nat
    trueRemainingCost : Endpoint → Nat

    -- Admissibility is a nonvacuous numeric bound, but a supplied
    -- 'trueRemainingCost' must still be welded to the actual graph
    -- shortest-distance semantics before claiming an A* search theorem.
    heuristicAdmissible :
      (n : Endpoint) → heuristic n ≤ trueRemainingCost n
    targetCostZero : trueRemainingCost target ≡ zero

-- The path cost is calculated from source-selected edge weights.
pathCost : (s : SearchProblem) {x y : Endpoint} →
  Route (SearchProblem.graph s) x y → Nat
pathCost s here = zero
pathCost s (step e tail) =
  SearchProblem.edgeCost s e + pathCost s tail

-- An executable search producer must return a route plus the
-- exact computed cost; no arbitrary Set-valued cost evidence.
record SearchResult (s : SearchProblem) : Set where
  constructor searchResult
  open SearchProblem s
  field
    path : Route graph start target
    reportedCost : Nat
    exactPathCostEvidence : reportedCost ≡ pathCost s path

-- The optimality receipt quantifies over EVERY rival route using
-- actual costs. It is not derived from a tie-order code alone.
record OptimalSearchResult (s : SearchProblem) : Set where
  constructor optimalSearchResult
  open SearchProblem s
  field
    candidate : SearchResult s
    allRivalCostsCovered :
      (rival : Route graph start target) →
      SearchResult.reportedCost candidate ≤ pathCost s rival

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
