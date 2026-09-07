module DASHI.Law.HerzogColonialWrongTypeLiveSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Cognition.PNF.SensibLawWrongTypeLiveResidualSchedulerExact as Scheduler
import DASHI.Law.HerzogColonialWrongTypeCrossSystemBridgeExact as Cross
import DASHI.Law.HerzogColonialWrongTypeExecutableSalienceFrontierExact as Frontier

------------------------------------------------------------------------
-- HERZOG x COLONIAL WRONGTYPE LIVE SCHEDULER
--
-- The first three analytical mechanism debts are selected from the executable
-- live-fibre salience frontier. Downstream applicability / violation / remedy
-- remain separate legal consumers after the analytical frontier closes.
------------------------------------------------------------------------

record HerzogWrongTypeSchedulerState : Set where
  constructor herzogWrongTypeSchedulerState
  field
    authorityMeaningClosed : Bool
    powerPrerequisiteClosed : Bool
    incidentWeldClosed : Bool
    applicabilityClosed : Bool
    violationClosed : Bool
    liabilityRemedyClosed : Bool

open HerzogWrongTypeSchedulerState public

currentHerzogWrongTypeState : HerzogWrongTypeSchedulerState
currentHerzogWrongTypeState = herzogWrongTypeSchedulerState
  false false false false false false

afterAuthorityMeaningState : HerzogWrongTypeSchedulerState
afterAuthorityMeaningState = herzogWrongTypeSchedulerState
  true false false false false false

afterPowerPrerequisiteState : HerzogWrongTypeSchedulerState
afterPowerPrerequisiteState = herzogWrongTypeSchedulerState
  true true false false false false

afterMechanismState : HerzogWrongTypeSchedulerState
afterMechanismState = herzogWrongTypeSchedulerState
  true true true false false false

afterApplicabilityState : HerzogWrongTypeSchedulerState
afterApplicabilityState = herzogWrongTypeSchedulerState
  true true true true false false

afterViolationState : HerzogWrongTypeSchedulerState
afterViolationState = herzogWrongTypeSchedulerState
  true true true true true false

analyticalPhase : HerzogWrongTypeSchedulerState → Frontier.AnalyticalSaliencePhase
analyticalPhase (herzogWrongTypeSchedulerState false p i a v l) =
  Frontier.initialAuthorityMeaningPhase
analyticalPhase (herzogWrongTypeSchedulerState true false i a v l) =
  Frontier.afterAuthorityMeaningPhase
analyticalPhase (herzogWrongTypeSchedulerState true true false a v l) =
  Frontier.afterPowerPrerequisitePhase
analyticalPhase (herzogWrongTypeSchedulerState true true true a v l) =
  Frontier.afterAnalyticalMechanismPhase

analyticalFrontier : HerzogWrongTypeSchedulerState → Frontier.AnalyticalFrontier
analyticalFrontier state = Frontier.selectFrontier (analyticalPhase state)

analyticalDiscriminator : HerzogWrongTypeSchedulerState → Scheduler.LegalDiscriminator
analyticalDiscriminator state = Frontier.frontierDiscriminator (analyticalFrontier state)

nextResidual : HerzogWrongTypeSchedulerState → Scheduler.LegalLiveResidual
nextResidual (herzogWrongTypeSchedulerState false p i a v l) = Scheduler.authorityMeaningOpen
nextResidual (herzogWrongTypeSchedulerState true false i a v l) = Scheduler.operationalPrerequisiteOpen
nextResidual (herzogWrongTypeSchedulerState true true false a v l) = Scheduler.sameObjectIncidentWeldOpen
nextResidual (herzogWrongTypeSchedulerState true true true false v l) = Scheduler.applicabilityOpen
nextResidual (herzogWrongTypeSchedulerState true true true true false l) = Scheduler.violationOpen
nextResidual (herzogWrongTypeSchedulerState true true true true true false) = Scheduler.liabilityRemedyOpen
nextResidual (herzogWrongTypeSchedulerState true true true true true true) = Scheduler.consumerActionClosed

nextDiscriminator : HerzogWrongTypeSchedulerState → Scheduler.LegalDiscriminator
nextDiscriminator (herzogWrongTypeSchedulerState false p i a v l) =
  analyticalDiscriminator (herzogWrongTypeSchedulerState false p i a v l)
nextDiscriminator (herzogWrongTypeSchedulerState true false i a v l) =
  analyticalDiscriminator (herzogWrongTypeSchedulerState true false i a v l)
nextDiscriminator (herzogWrongTypeSchedulerState true true false a v l) =
  analyticalDiscriminator (herzogWrongTypeSchedulerState true true false a v l)
nextDiscriminator (herzogWrongTypeSchedulerState true true true false v l) = Scheduler.proveApplicability
nextDiscriminator (herzogWrongTypeSchedulerState true true true true false l) = Scheduler.proveViolation
nextDiscriminator (herzogWrongTypeSchedulerState true true true true true false) = Scheduler.inspectLiabilityRemedy
nextDiscriminator (herzogWrongTypeSchedulerState true true true true true true) = Scheduler.stopForConsumer

currentAnalyticalFrontierIsAuthorityMeaning :
  analyticalFrontier currentHerzogWrongTypeState ≡ Frontier.authorityMeaningFrontier
currentAnalyticalFrontierIsAuthorityMeaning = refl

currentNextMoveIsAuthorityMeaningEvidence :
  nextDiscriminator currentHerzogWrongTypeState
  ≡ Scheduler.recoverAuthorityMeaningEvidence
currentNextMoveIsAuthorityMeaningEvidence = refl

afterAuthorityMeaningFrontierBecomesPower :
  analyticalFrontier afterAuthorityMeaningState ≡ Frontier.powerPrerequisiteFrontier
afterAuthorityMeaningFrontierBecomesPower = refl

afterAuthorityMeaningNextMoveChanges :
  nextDiscriminator afterAuthorityMeaningState
  ≡ Scheduler.inspectPowerPrerequisite
afterAuthorityMeaningNextMoveChanges = refl

afterPowerPrerequisiteFrontierBecomesIncident :
  analyticalFrontier afterPowerPrerequisiteState ≡ Frontier.incidentWeldFrontier
afterPowerPrerequisiteFrontierBecomesIncident = refl

afterPowerPrerequisiteNextMoveIsIncidentWeld :
  nextDiscriminator afterPowerPrerequisiteState
  ≡ Scheduler.recoverIncidentWeldEvidence
afterPowerPrerequisiteNextMoveIsIncidentWeld = refl

afterMechanismAnalyticalFrontierIsClosed :
  analyticalFrontier afterMechanismState ≡ Frontier.analyticalFrontierClosed
afterMechanismAnalyticalFrontierIsClosed = refl

afterMechanismNextMoveIsApplicability :
  nextDiscriminator afterMechanismState ≡ Scheduler.proveApplicability
afterMechanismNextMoveIsApplicability = refl

afterApplicabilityNextMoveIsViolation :
  nextDiscriminator afterApplicabilityState ≡ Scheduler.proveViolation
afterApplicabilityNextMoveIsViolation = refl

afterViolationNextMoveIsRemedyAudit :
  nextDiscriminator afterViolationState ≡ Scheduler.inspectLiabilityRemedy
afterViolationNextMoveIsRemedyAudit = refl

------------------------------------------------------------------------
-- Current source receipts force the first three translations to remain open.
------------------------------------------------------------------------

currentAuthorityTranslationOpen :
  Cross.translationStatus Cross.currentHerzogAuthorityErasureTranslation
  ≡ Cross.translationOpen
currentAuthorityTranslationOpen = refl

currentPowerTranslationOpen :
  Cross.translationStatus Cross.currentHerzogPrerequisiteTranslation
  ≡ Cross.translationOpen
currentPowerTranslationOpen = refl

currentIncidentTranslationOpen :
  Cross.translationStatus Cross.currentHerzogIncidentTranslation
  ≡ Cross.translationOpen
currentIncidentTranslationOpen = refl

------------------------------------------------------------------------
-- Pareto/cost donor is reused explicitly. Legal scheduling does not invent a
-- different meaning of gain just because the moves are documentary/doctrinal.
------------------------------------------------------------------------

costGainParetoSurfaceIsGeneric :
  Costed.CostedResidualChoiceBoundary.costAndGainCanDefineAParetoSurface
    Costed.canonicalCostedResidualChoiceBoundary ≡ true
costGainParetoSurfaceIsGeneric = refl

heterogeneousLegalMovesShareResidualObjective :
  Costed.CostedResidualChoiceBoundary.heterogeneousInformationMovesCanShareResidualObjective
    Costed.canonicalCostedResidualChoiceBoundary ≡ true
heterogeneousLegalMovesShareResidualObjective = refl

------------------------------------------------------------------------
-- Current stopping state.
------------------------------------------------------------------------

currentConsumerActionClosed : Bool
currentConsumerActionClosed = false

currentConsumerActionClosedIsFalse : currentConsumerActionClosed ≡ false
currentConsumerActionClosedIsFalse = refl

record HerzogLegalStoppingBoundary : Set where
  constructor herzogLegalStoppingBoundary
  field
    multipleHistoricalMechanismsMayRemainLiveAtConsumerClosure : Bool
    multipleHistoricalMechanismsMayRemainLiveAtConsumerClosureIsTrue :
      multipleHistoricalMechanismsMayRemainLiveAtConsumerClosure ≡ true
    actionAgreementCreatesLegalAuthority : Bool
    actionAgreementCreatesLegalAuthorityIsFalse : actionAgreementCreatesLegalAuthority ≡ false
    currentOpenTranslationPermitsStop : Bool
    currentOpenTranslationPermitsStopIsFalse : currentOpenTranslationPermitsStop ≡ false

canonicalHerzogLegalStoppingBoundary : HerzogLegalStoppingBoundary
canonicalHerzogLegalStoppingBoundary =
  herzogLegalStoppingBoundary true refl false refl false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AuthorityMeaningEvidenceMustBeRepeatedAfterClosure : Set where
data HistoricalColonialSimilarityIsEnoughToSkipMechanismEvidence : Set where
data AnalyticalFrontierOrderIsEntailmentOrder : Set where
data AnalyticalMechanismClosureSkipsApplicability : Set where
data ApplicabilityClosureSkipsViolation : Set where
data ViolationClosureSkipsRemedy : Set where

closedCoordinateDoesNotNeedRepeat : AuthorityMeaningEvidenceMustBeRepeatedAfterClosure → ⊥
closedCoordinateDoesNotNeedRepeat ()

historicalAnalogyCannotSkipModernEvidence :
  HistoricalColonialSimilarityIsEnoughToSkipMechanismEvidence → ⊥
historicalAnalogyCannotSkipModernEvidence ()

frontierOrderDoesNotCreateEntailment : AnalyticalFrontierOrderIsEntailmentOrder → ⊥
frontierOrderDoesNotCreateEntailment ()

mechanismDoesNotSkipApplicability : AnalyticalMechanismClosureSkipsApplicability → ⊥
mechanismDoesNotSkipApplicability ()

applicabilityDoesNotSkipViolation : ApplicabilityClosureSkipsViolation → ⊥
applicabilityDoesNotSkipViolation ()

violationDoesNotSkipRemedy : ViolationClosureSkipsRemedy → ⊥
violationDoesNotSkipRemedy ()
