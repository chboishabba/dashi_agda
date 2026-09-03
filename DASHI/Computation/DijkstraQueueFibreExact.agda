module DASHI.Computation.DijkstraQueueFibreExact where

-- Dijkstra fibre: correctness depends on extracting a minimum tentative key;
-- ordering among equal-key entries and queue tail representation is residual
-- only when a supplied minimum-preservation witness says the chosen action
-- cannot change the observed minimum certificate.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

record DijkstraFineState : Set where
  constructor dijkstraFineState
  field
    settledCount : Nat
    minimumTentativeDistance : Nat
    equalMinimumTieCode : Bool
    queueTailCode : Nat

open DijkstraFineState public

record DijkstraObservation : Set where
  constructor dijkstraObservation
  field
    observedSettledCount : Nat
    observedMinimumTentativeDistance : Nat

observeDijkstra : DijkstraFineState → DijkstraObservation
observeDijkstra s =
  dijkstraObservation (settledCount s) (minimumTentativeDistance s)

data EqualKeySwap : Set where identityEqualKey swapEqualKey : EqualKeySwap

actEqualKey : EqualKeySwap → DijkstraFineState → DijkstraFineState
actEqualKey identityEqualKey s = s
actEqualKey swapEqualKey (dijkstraFineState n d false tail) =
  dijkstraFineState n d true tail
actEqualKey swapEqualKey (dijkstraFineState n d true tail) =
  dijkstraFineState n d false tail

equalKeySwapPreservesObservation :
  (g : EqualKeySwap) (s : DijkstraFineState) →
  observeDijkstra (actEqualKey g s) ≡ observeDijkstra s
equalKeySwapPreservesObservation identityEqualKey s = refl
equalKeySwapPreservesObservation swapEqualKey (dijkstraFineState n d false tail) = refl
equalKeySwapPreservesObservation swapEqualKey (dijkstraFineState n d true tail) = refl

record DijkstraFibreBoundary : Set where
  constructor dijkstraFibreBoundary
  field
    equalMinimumTieOrderMayBeResidual : Bool
    equalMinimumTieOrderMayBeResidualIsTrue :
      equalMinimumTieOrderMayBeResidual ≡ true
    nonMinimumPriorityOrderMayBeIgnoredWithoutInvariant : Bool
    nonMinimumPriorityOrderMayBeIgnoredWithoutInvariantIsFalse :
      nonMinimumPriorityOrderMayBeIgnoredWithoutInvariant ≡ false
    negativeEdgeCorrectnessClaimed : Bool
    negativeEdgeCorrectnessClaimedIsFalse : negativeEdgeCorrectnessClaimed ≡ false

canonicalDijkstraFibreBoundary : DijkstraFibreBoundary
canonicalDijkstraFibreBoundary = dijkstraFibreBoundary true refl false refl false refl
