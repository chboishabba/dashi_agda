module DASHI.Governance.AnomalousConsumerIndexedObligationFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.ActiveObligationEvidenceFibreExact as Active
import DASHI.Core.RequiredAxisSupportSquareExact as Required
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory
import DASHI.Governance.PhenomenonEvidenceLadderProjectionOverTimeExact as Ladder

------------------------------------------------------------------------
-- CONSUMER-INDEXED ACTIVE OBLIGATION FIBRE OVER TEMPORAL EVIDENCE FIBRES
--
-- Evidence obligations are not global.  They depend jointly on:
--   phenomenon × evidence-time × declared consumer/query × evidence axis.
-- Inactive axes do not count as failures.  A missing active axis blocks only
-- the declared consumer that requires it.
------------------------------------------------------------------------

data EvidenceConsumer : Set where
  phenomenologyConsumer
  anomalyConsumer
  replicationConsumer
  mechanismConsumer
  operationalUtilityConsumer
  therapeuticConsumer
  ontologicalConsumer
  : EvidenceConsumer

ActiveAxis :
  Trajectory.EvidenceMoment → EvidenceConsumer → Temporal.EvidenceCoordinate → Set

-- Phenomenology consumers require report reliability.
ActiveAxis _ phenomenologyConsumer Temporal.reportReliability = ⊤

-- Anomaly consumers require anomaly strength and controls.
ActiveAxis _ anomalyConsumer Temporal.anomalyStrength = ⊤
ActiveAxis _ anomalyConsumer Temporal.controlStrength = ⊤

-- Replication consumers require controls and independent replication.
ActiveAxis _ replicationConsumer Temporal.controlStrength = ⊤
ActiveAxis _ replicationConsumer Temporal.independentReplication = ⊤

-- Mechanism consumers require a replicated effect plus mechanism separation.
ActiveAxis _ mechanismConsumer Temporal.independentReplication = ⊤
ActiveAxis _ mechanismConsumer Temporal.mechanismDiscrimination = ⊤

-- Operational utility requires replication, generalisation and direct utility.
ActiveAxis _ operationalUtilityConsumer Temporal.independentReplication = ⊤
ActiveAxis _ operationalUtilityConsumer Temporal.generalisation = ⊤
ActiveAxis _ operationalUtilityConsumer Temporal.operationalUtility = ⊤

-- Therapeutic consumer asks for controls, replication and generalisation.
ActiveAxis _ therapeuticConsumer Temporal.controlStrength = ⊤
ActiveAxis _ therapeuticConsumer Temporal.independentReplication = ⊤
ActiveAxis _ therapeuticConsumer Temporal.generalisation = ⊤

-- Ontological interpretation is the strongest consumer here: mechanism,
-- generalisation and ontological inference are all active.
ActiveAxis _ ontologicalConsumer Temporal.mechanismDiscrimination = ⊤
ActiveAxis _ ontologicalConsumer Temporal.generalisation = ⊤
ActiveAxis _ ontologicalConsumer Temporal.ontologicalInference = ⊤

ActiveAxis _ _ _ = ⊥

------------------------------------------------------------------------
-- Convert the existing time-sliced ladder into the support-square currency
-- expected by ActiveObligationEvidenceFibreExact.
--
-- This is deliberately conservative:
--   empiricallySupported -> positive-only
--   unsupported/downgraded -> negative-only
--   contested -> conflicting
--   unresolved/sourceReported -> missing for resolution purposes
------------------------------------------------------------------------

standingSupport : Temporal.CoordinateStanding → Required.SupportSquare
standingSupport Temporal.empiricallySupported = Required.supportSquare true false
standingSupport Temporal.unsupported = Required.supportSquare false true
standingSupport Temporal.downgraded = Required.supportSquare false true
standingSupport Temporal.contested = Required.supportSquare true true
standingSupport Temporal.unresolved = Required.supportSquare false false
standingSupport Temporal.sourceReported = Required.supportSquare false false

EvidenceAt :
  Trajectory.EvidenceMoment → EvidenceConsumer → Temporal.EvidenceCoordinate →
  Required.SupportSquare
EvidenceAt moment _ axis = standingSupport (Ladder.standingAt moment axis)

obligationFamily :
  Active.ActiveObligationFamily
    Trajectory.EvidenceMoment
    EvidenceConsumer
    Temporal.EvidenceCoordinate
obligationFamily = Active.activeObligationFamily ActiveAxis EvidenceAt

------------------------------------------------------------------------
-- Concrete consumer-relative open obligations.
------------------------------------------------------------------------

-- Current Bem mechanism consumer remains blocked: the mechanism axis is
-- unresolved, and replication has been downgraded.
bemMechanismMissing :
  Active.MissingActiveObligation
    obligationFamily
    Trajectory.transparentPsi2025
    mechanismConsumer
bemMechanismMissing =
  Active.missingActiveObligation
    Temporal.mechanismDiscrimination
    tt
    (refl , refl)

bemMechanismNotResolved :
  Active.ResolvedFor obligationFamily Trajectory.transparentPsi2025 mechanismConsumer → ⊥
bemMechanismNotResolved =
  Active.missingActiveObligationBlocksResolution bemMechanismMissing

-- NDE phenomenology can be supported while the mechanism consumer remains
-- open.  This is the central consumer-relative separation.
ndePhenomenologyResolved :
  Active.ResolvedFor obligationFamily Trajectory.awareII2023 phenomenologyConsumer
ndePhenomenologyResolved Temporal.reportReliability tt = refl , refl
ndePhenomenologyResolved Temporal.anomalyStrength ()
ndePhenomenologyResolved Temporal.controlStrength ()
ndePhenomenologyResolved Temporal.independentReplication ()
ndePhenomenologyResolved Temporal.mechanismDiscrimination ()
ndePhenomenologyResolved Temporal.generalisation ()
ndePhenomenologyResolved Temporal.operationalUtility ()
ndePhenomenologyResolved Temporal.ontologicalInference ()

ndeMechanismMissing :
  Active.MissingActiveObligation
    obligationFamily
    Trajectory.awareII2023
    mechanismConsumer
ndeMechanismMissing =
  Active.missingActiveObligation
    Temporal.mechanismDiscrimination
    tt
    (refl , refl)

ndeMechanismNotResolved :
  Active.ResolvedFor obligationFamily Trajectory.awareII2023 mechanismConsumer → ⊥
ndeMechanismNotResolved =
  Active.missingActiveObligationBlocksResolution ndeMechanismMissing

-- Psilocybin therapeutic evidence has positive independent-replication support
-- while controls remain conflicting, so a strict positive-resolution consumer
-- is intentionally still open.
psilocybinControlConflict :
  Required.ConflictingEvidence
    (EvidenceAt Trajectory.psilocybinMeta2025_2026 therapeuticConsumer Temporal.controlStrength)
psilocybinControlConflict = refl , refl

------------------------------------------------------------------------
-- Positive evidence on one active axis cannot compensate for another active
-- axis that is missing or conflicting.
------------------------------------------------------------------------

ndeReportSupportDoesNotFillMechanismAxis :
  Active.ResolvedFor obligationFamily Trajectory.awareII2023 mechanismConsumer → ⊥
ndeReportSupportDoesNotFillMechanismAxis = ndeMechanismNotResolved

psilocybinReplicationDoesNotByItselfCloseTherapeuticConsumer :
  Active.ResolvedFor obligationFamily Trajectory.psilocybinMeta2025_2026 therapeuticConsumer → ⊥
psilocybinReplicationDoesNotByItselfCloseTherapeuticConsumer resolved =
  Required.conflictingCannotBeResolvedPositive
    psilocybinControlConflict
    (resolved Temporal.controlStrength tt)

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data InactiveAxisCountsAsFailure : Set where

data PhenomenologyClosurePromotesMechanismClosure : Set where

data ReplicationSupportCompensatesForConflictingControls : Set where

data ConsumerQueryErasesTemporalFibre : Set where

inactiveAxisDoesNotCountAsFailure : InactiveAxisCountsAsFailure → ⊥
inactiveAxisDoesNotCountAsFailure ()

phenomenologyClosureDoesNotPromoteMechanismClosure :
  PhenomenologyClosurePromotesMechanismClosure → ⊥
phenomenologyClosureDoesNotPromoteMechanismClosure ()

replicationDoesNotCompensateForConflictingControls :
  ReplicationSupportCompensatesForConflictingControls → ⊥
replicationDoesNotCompensateForConflictingControls ()

consumerQueryDoesNotEraseTemporalFibre : ConsumerQueryErasesTemporalFibre → ⊥
consumerQueryDoesNotEraseTemporalFibre ()

record AnomalousConsumerIndexedObligationBoundary : Set where
  constructor anomalousConsumerIndexedObligationBoundary
  field
    activeObligationsDependOnTimeAndQuery : Bool
    activeObligationsDependOnTimeAndQueryIsTrue :
      activeObligationsDependOnTimeAndQuery ≡ true
    inactiveAxesCountAsFailures : Bool
    inactiveAxesCountAsFailuresIsFalse : inactiveAxesCountAsFailures ≡ false
    onePositiveAxisCompensatesForMissingRequiredAxis : Bool
    onePositiveAxisCompensatesForMissingRequiredAxisIsFalse :
      onePositiveAxisCompensatesForMissingRequiredAxis ≡ false
    phenomenologyClosureAutomaticallyClosesMechanism : Bool
    phenomenologyClosureAutomaticallyClosesMechanismIsFalse :
      phenomenologyClosureAutomaticallyClosesMechanism ≡ false

canonicalAnomalousConsumerIndexedObligationBoundary :
  AnomalousConsumerIndexedObligationBoundary
canonicalAnomalousConsumerIndexedObligationBoundary =
  anomalousConsumerIndexedObligationBoundary
    true refl false refl false refl false refl
