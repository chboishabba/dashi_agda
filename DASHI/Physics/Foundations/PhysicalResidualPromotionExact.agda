{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PhysicalResidualPromotionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as Ledger

------------------------------------------------------------------------
-- PHYSICAL RESIDUAL PROMOTION
--
-- A non-zero residual is an observation relative to an admitted-channel set.
-- It is not a mechanism label.  Stronger promotion classes require explicit
-- nuisance closure, repeatability, scaling, apparatus-change and independent
-- replication receipts tied to the exact candidate being promoted.
------------------------------------------------------------------------

data NuisanceClosureStatus : Set where
  nuisanceOpen : NuisanceClosureStatus
  nuisancePartiallyClosed : NuisanceClosureStatus
  nuisanceClosedByReceipt : NuisanceClosureStatus

record ResidualReplicationEvidence : Set where
  constructor residual-replication-evidence
  field
    repeatedOnSameApparatus : Bool
    predictiveScalingObserved : Bool
    survivesApparatusChange : Bool
    independentlyReplicated : Bool
    evidenceReference : String

open ResidualReplicationEvidence public

record AnomalousMomentumCandidate : Set where
  constructor anomalous-momentum-candidate
  field
    ledger : Ledger.ResidualLedger
    nuisanceStatus : NuisanceClosureStatus
    replication : ResidualReplicationEvidence
    remainsMechanismNeutral : Bool

open AnomalousMomentumCandidate public

canonicalReplicationEvidence : ResidualReplicationEvidence
canonicalReplicationEvidence =
  residual-replication-evidence false false false false
    "fixture: no replication authority"

canonicalAnomalousMomentumCandidate : AnomalousMomentumCandidate
canonicalAnomalousMomentumCandidate =
  anomalous-momentum-candidate
    Ledger.canonicalResidualLedger
    nuisanceOpen
    canonicalReplicationEvidence
    true

------------------------------------------------------------------------
-- No direct promotion permissions are exported.  These types deliberately
-- have no constructors: additional domain-specific evidence must enter through
-- a stronger owner rather than a cast from residual magnitude.
------------------------------------------------------------------------

data ResidualDirectAntigravityPermission : Set where
data ResidualDirectReactionlessPermission : Set where
data ResidualDirectNewPhysicsPermission : Set where

record StrongResidualPromotionEvidence
    (candidate : AnomalousMomentumCandidate) : Set where
  constructor strong-residual-promotion-evidence
  field
    candidateNuisanceClosed :
      nuisanceStatus candidate ≡ nuisanceClosedByReceipt

    candidateRepeatedIsTrue :
      repeatedOnSameApparatus (replication candidate) ≡ true

    candidateScalingIsTrue :
      predictiveScalingObserved (replication candidate) ≡ true

    candidateApparatusChangeIsTrue :
      survivesApparatusChange (replication candidate) ≡ true

    candidateIndependentReplicationIsTrue :
      independentlyReplicated (replication candidate) ≡ true

    candidateRemainsMechanismNeutral :
      remainsMechanismNeutral candidate ≡ true

    sameObjectCalibrationReference : String

open StrongResidualPromotionEvidence public

record ResidualPromotionBoundary : Set where
  constructor residual-promotion-boundary
  field
    residualDoesNotDirectlyPromoteToAntigravity : Bool
    residualDoesNotDirectlyPromoteToReactionless : Bool
    residualDoesNotDirectlyPromoteToNewPhysics : Bool
    missingNuisanceChannelBlocksClosure : Bool
    gravityNeedsIndependentMetricOrGravityConsumer : Bool
    mechanismPromotionNeedsSeparateEvidence : Bool
    strongPromotionRequiresProofCarryingReplication : Bool
    strongEvidenceMustReferToExactCandidate : Bool

open ResidualPromotionBoundary public

canonicalResidualPromotionBoundary : ResidualPromotionBoundary
canonicalResidualPromotionBoundary =
  residual-promotion-boundary true true true true true true true true
