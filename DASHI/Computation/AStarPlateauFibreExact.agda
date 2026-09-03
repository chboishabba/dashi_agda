module DASHI.Computation.AStarPlateauFibreExact where

-- A* fibre: ordering inside an equal-f plateau may be residual for a consumer
-- that observes only the current minimum f-bound, but only under an explicit
-- heuristic/correctness contract.  This owner does not claim arbitrary
-- heuristic tie-breaking is correctness-neutral.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

record AStarFineState : Set where
  constructor aStarFineState
  field
    expandedCount : Nat
    minimumFScore : Nat
    plateauTieCode : Bool
    openTailCode : Nat

open AStarFineState public

record AStarObservation : Set where
  constructor aStarObservation
  field observedExpandedCount observedMinimumFScore : Nat

observeAStar : AStarFineState → AStarObservation
observeAStar s = aStarObservation (expandedCount s) (minimumFScore s)

data PlateauSwap : Set where identityPlateau swapPlateauTie : PlateauSwap

actPlateau : PlateauSwap → AStarFineState → AStarFineState
actPlateau identityPlateau s = s
actPlateau swapPlateauTie (aStarFineState n f false tail) =
  aStarFineState n f true tail
actPlateau swapPlateauTie (aStarFineState n f true tail) =
  aStarFineState n f false tail

plateauSwapPreservesObservation :
  (g : PlateauSwap) (s : AStarFineState) →
  observeAStar (actPlateau g s) ≡ observeAStar s
plateauSwapPreservesObservation identityPlateau s = refl
plateauSwapPreservesObservation swapPlateauTie (aStarFineState n f false tail) = refl
plateauSwapPreservesObservation swapPlateauTie (aStarFineState n f true tail) = refl

record AStarCorrectnessContract : Set where
  constructor aStarCorrectnessContract
  field
    heuristicAdmissibilitySupplied : Bool
    plateauResidualLawSupplied : Bool

record AStarFibreBoundary : Set where
  constructor aStarFibreBoundary
  field
    equalFPlateauCanCarryResidualOrder : Bool
    equalFPlateauCanCarryResidualOrderIsTrue :
      equalFPlateauCanCarryResidualOrder ≡ true
    admissibilityMayBeOmitted : Bool
    admissibilityMayBeOmittedIsFalse : admissibilityMayBeOmitted ≡ false
    arbitraryTieBreakingAlwaysPreservesExpansionTrace : Bool
    arbitraryTieBreakingAlwaysPreservesExpansionTraceIsFalse :
      arbitraryTieBreakingAlwaysPreservesExpansionTrace ≡ false

canonicalAStarFibreBoundary : AStarFibreBoundary
canonicalAStarFibreBoundary = aStarFibreBoundary true refl false refl false refl
