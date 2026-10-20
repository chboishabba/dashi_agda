module DASHI.Biology.BH4IntervalFluxSolverExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Interval feasibility solver boundary.
--
-- The executable solver searches for one steady-state witness satisfying
-- S*v + e = 0 together with source-paid lower/upper bounds on every reaction
-- flux and every species exchange coordinate. Missing bounds are not widened to
-- zero/infinity silently: the outcome is underdetermined. Solver availability
-- is also explicit.
------------------------------------------------------------------------

data IntervalFluxSolverStatus : Set where
  feasible : IntervalFluxSolverStatus
  infeasible : IntervalFluxSolverStatus
  underdetermined : IntervalFluxSolverStatus
  solverUnavailable : IntervalFluxSolverStatus

record IntervalFluxSolveReceipt : Set where
  constructor interval-flux-solve-receipt
  field
    matrixReference : String
    parameterReference : String
    status : IntervalFluxSolverStatus
    reactionVariables : Nat
    exchangeVariables : Nat
    missingReactionBounds : Nat
    missingExchangeBounds : Nat
    witnessReference : String

open IntervalFluxSolveReceipt public

canonicalPreRunIntervalReceipt : IntervalFluxSolveReceipt
canonicalPreRunIntervalReceipt =
  interval-flux-solve-receipt
    "executed 29x12 BH4 matrix"
    "matrix-aware quantitative parameter manifest"
    underdetermined
    12 29 12 29
    "no interval witness before quantitative bounds are source-paid"

jointFluxStatusTypeAvailable : Set
jointFluxStatusTypeAvailable = Flux.FluxFeasibilityStatus

record IntervalFluxSolverBoundary : Set where
  constructor interval-flux-solver-boundary
  field
    missingReactionBoundMayBeSubstitutedWithZero : Bool
    missingReactionBoundMayBeSubstitutedWithZeroIsFalse :
      missingReactionBoundMayBeSubstitutedWithZero ≡ false
    missingExchangeBoundMayBeSubstitutedWithZero : Bool
    missingExchangeBoundMayBeSubstitutedWithZeroIsFalse :
      missingExchangeBoundMayBeSubstitutedWithZero ≡ false
    feasibleSteadyStateCreatesAllocatorCausality : Bool
    feasibleSteadyStateCreatesAllocatorCausalityIsFalse :
      feasibleSteadyStateCreatesAllocatorCausality ≡ false
    feasibleSteadyStateCreatesDiseaseMechanism : Bool
    feasibleSteadyStateCreatesDiseaseMechanismIsFalse :
      feasibleSteadyStateCreatesDiseaseMechanism ≡ false
    solverInfeasibleProvesAllDynamicStatesImpossible : Bool
    solverInfeasibleProvesAllDynamicStatesImpossibleIsFalse :
      solverInfeasibleProvesAllDynamicStatesImpossible ≡ false

open IntervalFluxSolverBoundary public

canonicalIntervalFluxSolverBoundary : IntervalFluxSolverBoundary
canonicalIntervalFluxSolverBoundary =
  interval-flux-solver-boundary false refl false refl false refl false refl false refl

canonicalBH4IntervalFluxSolverReceipt : Receipt.GenericReceipt
canonicalBH4IntervalFluxSolverReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 interval flux solver"
    "DASHI.Biology.BH4IntervalFluxSolverExact"
    "source-paid reaction/exchange intervals + executed stoichiometric matrix -> linear steady-state feasibility search"
    "searches for an admissible S*v+e=0 witness once every required interval is paid; missing bounds and unavailable solver are explicit statuses"
    "missing coordinates are not zero; steady-state feasibility is not allocator causality or disease mechanism; steady-state infeasibility is not global dynamic impossibility"
    "python3 scripts/solve_bh4_flux_intervals.py --help"
