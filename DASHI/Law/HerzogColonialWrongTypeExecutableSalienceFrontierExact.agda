module DASHI.Law.HerzogColonialWrongTypeExecutableSalienceFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawWrongTypeLiveResidualSchedulerExact as Scheduler
import DASHI.Law.HerzogColonialWrongTypeElementRequirementExact as Element

------------------------------------------------------------------------
-- EXECUTABLE REQUIREMENT-SALIENCE FRONTIER
--
-- Proof objects in HerzogColonialWrongTypeRequirementSalienceExact establish
-- why a requirement is salient or currently non-discriminating. This module is
-- the finite executable companion for the concrete three-coordinate portfolio.
--
-- Requiredness is NOT recomputed from salience. A false split flag means only
-- "not useful for distinguishing the CURRENT live interpretations".
------------------------------------------------------------------------

data AnalyticalSaliencePhase : Set where
  initialAuthorityMeaningPhase
  afterAuthorityMeaningPhase
  afterPowerPrerequisitePhase
  afterAnalyticalMechanismPhase
  : AnalyticalSaliencePhase

record RequirementFrontierCell : Set where
  constructor requirement-frontier-cell
  field
    requirement : Element.MechanismRequirementKind
    requiredForConsumer : Bool
    consumerRelevant : Bool
    authorityAdmissible : Bool
    splitsCurrentLiveFibre : Bool

open RequirementFrontierCell public

cellAt :
  AnalyticalSaliencePhase →
  Element.MechanismRequirementKind →
  RequirementFrontierCell
cellAt initialAuthorityMeaningPhase Element.requiresAuthorityMeaningErasure =
  requirement-frontier-cell Element.requiresAuthorityMeaningErasure true true true true
cellAt initialAuthorityMeaningPhase Element.requiresOperationalPrerequisite =
  requirement-frontier-cell Element.requiresOperationalPrerequisite true true true false
cellAt initialAuthorityMeaningPhase Element.requiresSameObjectProjectionPowerIncident =
  requirement-frontier-cell Element.requiresSameObjectProjectionPowerIncident true true true false

cellAt afterAuthorityMeaningPhase Element.requiresAuthorityMeaningErasure =
  requirement-frontier-cell Element.requiresAuthorityMeaningErasure true true true false
cellAt afterAuthorityMeaningPhase Element.requiresOperationalPrerequisite =
  requirement-frontier-cell Element.requiresOperationalPrerequisite true true true true
cellAt afterAuthorityMeaningPhase Element.requiresSameObjectProjectionPowerIncident =
  requirement-frontier-cell Element.requiresSameObjectProjectionPowerIncident true true true false

cellAt afterPowerPrerequisitePhase Element.requiresAuthorityMeaningErasure =
  requirement-frontier-cell Element.requiresAuthorityMeaningErasure true true true false
cellAt afterPowerPrerequisitePhase Element.requiresOperationalPrerequisite =
  requirement-frontier-cell Element.requiresOperationalPrerequisite true true true false
cellAt afterPowerPrerequisitePhase Element.requiresSameObjectProjectionPowerIncident =
  requirement-frontier-cell Element.requiresSameObjectProjectionPowerIncident true true true true

cellAt afterAnalyticalMechanismPhase requirement =
  requirement-frontier-cell requirement true true true false

_&&_ : Bool → Bool → Bool
false && right = false
true && right = right

isFrontierCell : RequirementFrontierCell → Bool
isFrontierCell cell =
  requiredForConsumer cell &&
  (consumerRelevant cell &&
   (authorityAdmissible cell && splitsCurrentLiveFibre cell))

data AnalyticalFrontier : Set where
  authorityMeaningFrontier
  powerPrerequisiteFrontier
  incidentWeldFrontier
  analyticalFrontierClosed
  : AnalyticalFrontier

selectFrontier : AnalyticalSaliencePhase → AnalyticalFrontier
selectFrontier phase with isFrontierCell (cellAt phase Element.requiresAuthorityMeaningErasure)
... | true = authorityMeaningFrontier
... | false with isFrontierCell (cellAt phase Element.requiresOperationalPrerequisite)
...   | true = powerPrerequisiteFrontier
...   | false with isFrontierCell (cellAt phase Element.requiresSameObjectProjectionPowerIncident)
...     | true = incidentWeldFrontier
...     | false = analyticalFrontierClosed

frontierDiscriminator : AnalyticalFrontier → Scheduler.LegalDiscriminator
frontierDiscriminator authorityMeaningFrontier = Scheduler.recoverAuthorityMeaningEvidence
frontierDiscriminator powerPrerequisiteFrontier = Scheduler.inspectPowerPrerequisite
frontierDiscriminator incidentWeldFrontier = Scheduler.recoverIncidentWeldEvidence
frontierDiscriminator analyticalFrontierClosed = Scheduler.proveApplicability

currentFrontier : AnalyticalFrontier
currentFrontier = selectFrontier initialAuthorityMeaningPhase

currentFrontierIsAuthorityMeaning : currentFrontier ≡ authorityMeaningFrontier
currentFrontierIsAuthorityMeaning = refl

currentFrontierMove : Scheduler.LegalDiscriminator
currentFrontierMove = frontierDiscriminator currentFrontier

currentFrontierMoveIsAuthorityMeaningRecovery :
  currentFrontierMove ≡ Scheduler.recoverAuthorityMeaningEvidence
currentFrontierMoveIsAuthorityMeaningRecovery = refl

afterAuthorityMeaningFrontier : AnalyticalFrontier
afterAuthorityMeaningFrontier = selectFrontier afterAuthorityMeaningPhase

afterAuthorityMeaningFrontierIsPowerPrerequisite :
  afterAuthorityMeaningFrontier ≡ powerPrerequisiteFrontier
afterAuthorityMeaningFrontierIsPowerPrerequisite = refl

afterAuthorityMeaningMove : Scheduler.LegalDiscriminator
afterAuthorityMeaningMove = frontierDiscriminator afterAuthorityMeaningFrontier

afterAuthorityMeaningMoveIsPowerAudit :
  afterAuthorityMeaningMove ≡ Scheduler.inspectPowerPrerequisite
afterAuthorityMeaningMoveIsPowerAudit = refl

afterPowerPrerequisiteFrontier : AnalyticalFrontier
afterPowerPrerequisiteFrontier = selectFrontier afterPowerPrerequisitePhase

afterPowerPrerequisiteFrontierIsIncidentWeld :
  afterPowerPrerequisiteFrontier ≡ incidentWeldFrontier
afterPowerPrerequisiteFrontierIsIncidentWeld = refl

afterMechanismFrontier : AnalyticalFrontier
afterMechanismFrontier = selectFrontier afterAnalyticalMechanismPhase

afterMechanismFrontierIsClosed :
  afterMechanismFrontier ≡ analyticalFrontierClosed
afterMechanismFrontierIsClosed = refl

afterMechanismMovesToApplicability :
  frontierDiscriminator afterMechanismFrontier ≡ Scheduler.proveApplicability
afterMechanismMovesToApplicability = refl

------------------------------------------------------------------------
-- Required-but-inert coordinates remain retained in the portfolio.
------------------------------------------------------------------------

powerStillRequiredInitially :
  requiredForConsumer
    (cellAt initialAuthorityMeaningPhase Element.requiresOperationalPrerequisite)
  ≡ true
powerStillRequiredInitially = refl

powerDoesNotSplitInitially :
  splitsCurrentLiveFibre
    (cellAt initialAuthorityMeaningPhase Element.requiresOperationalPrerequisite)
  ≡ false
powerDoesNotSplitInitially = refl

powerSplitsAfterAuthorityMeaning :
  splitsCurrentLiveFibre
    (cellAt afterAuthorityMeaningPhase Element.requiresOperationalPrerequisite)
  ≡ true
powerSplitsAfterAuthorityMeaning = refl

incidentStillRequiredBeforeSalient :
  requiredForConsumer
    (cellAt initialAuthorityMeaningPhase Element.requiresSameObjectProjectionPowerIncident)
  ≡ true
incidentStillRequiredBeforeSalient = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FalseSplitMeansNotRequired : Set where
data FrontierSelectionPaysRequirement : Set where
data FrontierOrderIsLogicalEntailment : Set where
data ClosedAnalyticalFrontierCreatesApplicability : Set where

falseSplitDoesNotEraseRequiredness : FalseSplitMeansNotRequired → ⊥
falseSplitDoesNotEraseRequiredness ()

selectionDoesNotPayRequirement : FrontierSelectionPaysRequirement → ⊥
selectionDoesNotPayRequirement ()

frontierOrderDoesNotCreateEntailment : FrontierOrderIsLogicalEntailment → ⊥
frontierOrderDoesNotCreateEntailment ()

analyticalFrontierClosureDoesNotProveApplicability :
  ClosedAnalyticalFrontierCreatesApplicability → ⊥
analyticalFrontierClosureDoesNotProveApplicability ()
