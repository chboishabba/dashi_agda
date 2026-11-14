module DASHI.Moonshine.OggSSPClimbingGymEmpiricalTerminalExact where

------------------------------------------------------------------------
-- EMPIRICAL TERMINAL CAPSTONE
--
-- This owner answers only the empirical question left after the structural
-- max-cut.  It composes the already-recorded results without strengthening
-- their authority.
--
-- Outcome:
-- * mutual-nearest saturation is non-Ogg-specific;
-- * the exploratory multiplicative Dirichlet-phase coherence tail from zeros
--   1..849 does not replicate on the locked disjoint 850..1698 window;
-- * the single predeclared native-address occupancy statistic is non-extreme
--   in both discovery and held-out windows;
-- * therefore the tested observables do not presently support an Ogg/Monster-
--   specific empirical anomaly;
-- * this null/falsification result is not a theorem that no such observable can
--   exist, and it says nothing against Monstrous Moonshine itself.
--
-- The rigorous FLINT/Arb phase-bundle producer/checker pipeline is source-
-- written but has not been executed in this environment, so the current
-- empirical conclusions still rest on the diagnostic numerical zero caches.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorResultExact as Address
import DASHI.Moonshine.OggSSPClimbingGymDirichletPhaseExact as Dirichlet
import DASHI.Moonshine.OggSSPClimbingGymEmpiricalReplayExact as Replay
import DASHI.Moonshine.OggSSPClimbingGymTerminalStatusExact as Status

record ClimbingGymEmpiricalTerminal : Set where
  constructor climbing-gym-empirical-terminal
  field
    tenFigureRowsReplayed : Bool
    nonOggSaturationObserved : Bool

    dirichletDiscoveryTailObserved : Bool
    dirichletDiscoveryTailReplicatesHeldOut : Bool

    nativeAddressDiscoveryTwoSidedTailCount : Nat
    nativeAddressHeldOutTwoSidedTailCount : Nat
    nativeAddressBalancedAssignmentCount : Nat
    nativeAddressBothWindowsNonExtreme : Bool

    rigorousPhaseBundleAvailable : Bool

    empiricalMonsterSpecificitySupported : Bool
    moonshineTheoremRefuted : Bool
    universalNoOggSignalTheoremProved : Bool
    riemannHypothesisPromoted : Bool

open ClimbingGymEmpiricalTerminal public

canonicalClimbingGymEmpiricalTerminal : ClimbingGymEmpiricalTerminal
canonicalClimbingGymEmpiricalTerminal =
  climbing-gym-empirical-terminal
    true
    true
    true
    false
    Address.discoveryTwoSidedTailCount
    Address.heldOutTwoSidedTailCount
    Address.balancedAssignmentCount
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Cross-owner consistency.
------------------------------------------------------------------------

dirichletHeldOutNonReplicationIsSourceReceipt :
  Dirichlet.heldOutReplicatedMonsterSpecificAnomaly
    Dirichlet.canonicalDirichletPhaseBoundary
  ≡ false
dirichletHeldOutNonReplicationIsSourceReceipt = refl

nativeAddressDiscoveryCountExact :
  nativeAddressDiscoveryTwoSidedTailCount canonicalClimbingGymEmpiricalTerminal
  ≡ 7074
nativeAddressDiscoveryCountExact = refl

nativeAddressHeldOutCountExact :
  nativeAddressHeldOutTwoSidedTailCount canonicalClimbingGymEmpiricalTerminal
  ≡ 10449
nativeAddressHeldOutCountExact = refl

rigorousBundleStillMarkedExternal :
  Status.rigorousExternalBundleExecuted Status.canonicalClimbingGymTerminalStatus
  ≡ false
rigorousBundleStillMarkedExternal = refl

sourceSeedStillNotRecovered :
  Replay.reportedShiftControlSeedRecovered Replay.canonicalClimbingGymReplayBoundary
  ≡ false
sourceSeedStillNotRecovered = refl
