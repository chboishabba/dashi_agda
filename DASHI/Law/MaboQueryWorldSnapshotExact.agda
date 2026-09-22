module DASHI.Law.MaboQueryWorldSnapshotExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.QueryWorldAutonomousRunControllerExact as Controller
import DASHI.Law.MaboGenericLegalFollowAdapterExact as Mabo
import DASHI.Law.ClosedIsNotAdequateExact as Closed

------------------------------------------------------------------------
-- S15/S16/S18 typed Mabo query/world snapshot.
--
-- The snapshot is a read-only carrier connecting the existing Mabo consumer to
-- the generic query-world controller.  It may report:
--
--   * all currently observed identities paid + operational closure
--   * an unresolved observed identity
--
-- but it cannot manufacture a FactorsThrough witness, identity payment,
-- semantic authority, or claim truth.
------------------------------------------------------------------------

data SnapshotIdentityState : Set where
  observedIdentitiesPaid : SnapshotIdentityState
  unresolvedObservedIdentity : SnapshotIdentityState

snapshotDecision :
  SnapshotIdentityState →
  Controller.RunDecision
snapshotDecision observedIdentitiesPaid =
  Controller.decide
    Controller.noWorldCoordinateChange
    Controller.noFormalWitness
snapshotDecision unresolvedObservedIdentity =
  Controller.reopenExactResearch

matureClosedSnapshotRequiresFreshAdequacyWitness :
  snapshotDecision observedIdentitiesPaid
  ≡
  Controller.requireFreshAdequacyWitness
matureClosedSnapshotRequiresFreshAdequacyWitness =
  Controller.sameWorldWithoutWitnessStillNeedsProof

unresolvedIdentitySnapshotReopensResearch :
  snapshotDecision unresolvedObservedIdentity
  ≡
  Controller.reopenExactResearch
unresolvedIdentitySnapshotReopensResearch = refl

data SnapshotAutomaticallyFactorsThrough : Set where
data SnapshotAutomaticallyPaysIdentity : Set where
data SnapshotAutomaticallyCreatesTruth : Set where

snapshotCannotConstructFactorsThrough :
  SnapshotAutomaticallyFactorsThrough → ⊥
snapshotCannotConstructFactorsThrough ()

snapshotCannotPayIdentity :
  SnapshotAutomaticallyPaysIdentity → ⊥
snapshotCannotPayIdentity ()

snapshotCannotCreateTruth :
  SnapshotAutomaticallyCreatesTruth → ⊥
snapshotCannotCreateTruth ()

maboBoundary :
  Mabo.MaboGenericLegalFollowAdapterBoundary
maboBoundary =
  Mabo.canonicalMaboGenericLegalFollowAdapterBoundary

closedBoundary :
  Closed.ClosedIsNotAdequateBoundary
closedBoundary =
  Closed.canonicalClosedIsNotAdequateBoundary

controllerBoundary :
  Controller.QueryWorldAutonomousRunControllerBoundary
controllerBoundary =
  Controller.canonicalQueryWorldAutonomousRunControllerBoundary

record MaboQueryWorldSnapshotBoundary : Set where
  constructor maboQueryWorldSnapshotBoundary
  field
    snapshotCarriesExplicitWorldCoordinates : Bool
    snapshotCarriesExplicitWorldCoordinatesIsTrue :
      snapshotCarriesExplicitWorldCoordinates ≡ true

    snapshotCarriesConsumerDemandAndCoverage : Bool
    snapshotCarriesConsumerDemandAndCoverageIsTrue :
      snapshotCarriesConsumerDemandAndCoverage ≡ true

    snapshotCarriesDependencySlice : Bool
    snapshotCarriesDependencySliceIsTrue :
      snapshotCarriesDependencySlice ≡ true

    closedMatureSnapshotWithoutWitnessIsConsumerAdequate : Bool
    closedMatureSnapshotWithoutWitnessIsConsumerAdequateIsFalse :
      closedMatureSnapshotWithoutWitnessIsConsumerAdequate ≡ false

    closedMatureSnapshotRequiresFreshAdequacyWitness : Bool
    closedMatureSnapshotRequiresFreshAdequacyWitnessIsTrue :
      closedMatureSnapshotRequiresFreshAdequacyWitness ≡ true

    unresolvedIdentitySnapshotMayPreserveClosure : Bool
    unresolvedIdentitySnapshotMayPreserveClosureIsFalse :
      unresolvedIdentitySnapshotMayPreserveClosure ≡ false

    snapshotUnresolvedIdentityReopensResearch : Bool
    snapshotUnresolvedIdentityReopensResearchIsTrue :
      snapshotUnresolvedIdentityReopensResearch ≡ true

    snapshotCreatesSemanticAuthority : Bool
    snapshotCreatesSemanticAuthorityIsFalse :
      snapshotCreatesSemanticAuthority ≡ false

    snapshotCreatesClaimTruth : Bool
    snapshotCreatesClaimTruthIsFalse :
      snapshotCreatesClaimTruth ≡ false

open MaboQueryWorldSnapshotBoundary public

canonicalMaboQueryWorldSnapshotBoundary :
  MaboQueryWorldSnapshotBoundary
canonicalMaboQueryWorldSnapshotBoundary =
  maboQueryWorldSnapshotBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
