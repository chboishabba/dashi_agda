module DASHI.Law.MaboQueryWorldSnapshotRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.MaboQueryWorldSnapshotExact as Snapshot
import DASHI.Law.QueryWorldAutonomousRunControllerExact as Controller

boundary : Snapshot.MaboQueryWorldSnapshotBoundary
boundary = Snapshot.canonicalMaboQueryWorldSnapshotBoundary

explicitWorld :
  Snapshot.snapshotCarriesExplicitWorldCoordinates boundary ≡ true
explicitWorld =
  Snapshot.snapshotCarriesExplicitWorldCoordinatesIsTrue boundary

demandCoveragePresent :
  Snapshot.snapshotCarriesConsumerDemandAndCoverage boundary ≡ true
demandCoveragePresent =
  Snapshot.snapshotCarriesConsumerDemandAndCoverageIsTrue boundary

dependencySlicePresent :
  Snapshot.snapshotCarriesDependencySlice boundary ≡ true
dependencySlicePresent =
  Snapshot.snapshotCarriesDependencySliceIsTrue boundary

closedIsNotAdequate :
  Snapshot.closedMatureSnapshotWithoutWitnessIsConsumerAdequate boundary ≡ false
closedIsNotAdequate =
  Snapshot.closedMatureSnapshotWithoutWitnessIsConsumerAdequateIsFalse boundary

closedNeedsFreshWitness :
  Snapshot.snapshotDecision Snapshot.observedIdentitiesPaid
  ≡
  Controller.requireFreshAdequacyWitness
closedNeedsFreshWitness =
  Snapshot.matureClosedSnapshotRequiresFreshAdequacyWitness

unresolvedReopens :
  Snapshot.snapshotDecision Snapshot.unresolvedObservedIdentity
  ≡
  Controller.reopenExactResearch
unresolvedReopens =
  Snapshot.unresolvedIdentitySnapshotReopensResearch
