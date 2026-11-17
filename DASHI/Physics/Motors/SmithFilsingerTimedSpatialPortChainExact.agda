module DASHI.Physics.Motors.SmithFilsingerTimedSpatialPortChainExact where

-- Reuses canonical finite causal flight and all-N spatial energy owners.
-- Time is explicitly part of the dependent chain topology. This is a
-- discrete timing theorem, not a relativistic signal-front Maxwell proof.
-- User hypothesis: phase/time control of Smith/Filsinger source-sink paths.
-- Physical propagation geometry, original clock and solar source OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact as Spatial

record CausalSpatialCell
  (incoming outgoing launchTime arrivalTime : Nat) : Set where
  constructor causalSpatialCell
  field
    work : Spatial.SpatialCell incoming outgoing
    flight : Time.RetardedFlight
    startsAt : Time.RetardedFlight.launch flight ≡ launchTime
    finishesAt : Time.RetardedFlight.arrival flight ≡ arrivalTime

data TimedSpatialChain : Nat → Nat → Nat → Nat → Set where
  emptyTimed : (boundary time : Nat) →
    TimedSpatialChain boundary boundary time time
  thenTimed : ∀ {first shared last start middle finish} →
    CausalSpatialCell first shared start middle →
    TimedSpatialChain shared last middle finish →
    TimedSpatialChain first last start finish

eraseTiming : ∀ {first last start finish} →
  TimedSpatialChain first last start finish →
  Spatial.SpatialChain first last
eraseTiming (emptyTimed boundary _) = Spatial.empty boundary
eraseTiming (thenTimed c rest) =
  Spatial.thenCell (CausalSpatialCell.work c) (eraseTiming rest)

substLower :
  ∀ {a b c : Nat} → a ≡ b → Bound._≤_ b c → Bound._≤_ a c
substLower refl proof = proof

cellArrivalNotBeforeLaunch :
  ∀ {first last start finish} →
  (c : CausalSpatialCell first last start finish) →
  Bound._≤_ start finish
cellArrivalNotBeforeLaunch c =
  Bound.transportUpper (CausalSpatialCell.finishesAt c)
    (substLower (sym (CausalSpatialCell.startsAt c))
      (Time.arrivalNoEarlier (CausalSpatialCell.flight c)))

reflOrder : (n : Nat) → Bound._≤_ n n
reflOrder zero = Bound.z≤n
reflOrder (suc n) = Bound.s≤s (reflOrder n)

allTimedPathsArriveAfterLaunch :
  ∀ {first last start finish} →
  TimedSpatialChain first last start finish →
  Bound._≤_ start finish
allTimedPathsArriveAfterLaunch (emptyTimed _ t) = reflOrder t
allTimedPathsArriveAfterLaunch (thenTimed c rest) =
  Cycle.≤-trans
    (cellArrivalNotBeforeLaunch c)
    (allTimedPathsArriveAfterLaunch rest)

-- All-N spatial energy conservation survives an explicitly timed path.
timedSpatialEnergyConservation :
  ∀ {first last start finish}
  (path : TimedSpatialChain first last start finish) →
  first + (Spatial.sumDrive (eraseTiming path)
    + Spatial.sumInitialStorage (eraseTiming path))
  ≡ last + (Spatial.sumUsefulLoad (eraseTiming path)
    + (Spatial.sumDissipation (eraseTiming path)
    + Spatial.sumFinalStorage (eraseTiming path)))
timedSpatialEnergyConservation path =
  Spatial.spatialChainWorkBalance (eraseTiming path)

-- Nonvacuous causal two-segment model: 1 + 2 = 3, 3 + 4 = 7.
-- The energy budgets are the exact previously constructed two-cell witness.
exampleTimedTwoCells : TimedSpatialChain 10 6 1 7
exampleTimedTwoCells =
  thenTimed
    (causalSpatialCell
      (Spatial.spatialCell 1 2 2 1 2 refl)
      (Time.scheduled 1 2) refl refl)
    (thenTimed
      (causalSpatialCell
        (Spatial.spatialCell 0 1 1 1 1 refl)
        (Time.scheduled 3 4) refl refl)
      (emptyTimed 6 7))

exampleArrivalOrder : Bound._≤_ 1 7
exampleArrivalOrder = allTimedPathsArriveAfterLaunch exampleTimedTwoCells

exampleTimedEnergy :
  10 + (Spatial.sumDrive (eraseTiming exampleTimedTwoCells)
     + Spatial.sumInitialStorage (eraseTiming exampleTimedTwoCells))
  ≡ 6 + (Spatial.sumUsefulLoad (eraseTiming exampleTimedTwoCells)
      + (Spatial.sumDissipation (eraseTiming exampleTimedTwoCells)
      + Spatial.sumFinalStorage (eraseTiming exampleTimedTwoCells)))
exampleTimedEnergy = timedSpatialEnergyConservation exampleTimedTwoCells
