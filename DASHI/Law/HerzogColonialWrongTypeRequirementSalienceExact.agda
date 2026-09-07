module DASHI.Law.HerzogColonialWrongTypeRequirementSalienceExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawWrongTypeRequirementSalienceFrontierExact as Frontier
import DASHI.Cognition.PNF.SensibLawWrongTypeLiveResidualSchedulerExact as Scheduler
import DASHI.Law.HerzogColonialWrongTypeElementRequirementExact as Element

------------------------------------------------------------------------
-- HERZOG / COLONIAL WRONGTYPE REQUIREMENT-SALIENCE FIXTURE
--
-- The analytical mechanism has three required coordinates. Their current
-- discrimination value is state-dependent. This file deliberately separates:
--
--   legally/analytically required
--
-- from
--
--   useful next discriminator on the current live interpretation fibre.
------------------------------------------------------------------------

data HerzogInterpretation : Set where
  securityClassificationOnly : HerzogInterpretation
  authorityErasureCandidate : HerzogInterpretation


data RequirementObservation : Set where
  unsupported unresolved supported : RequirementObservation

currentLiveInterpretations : HerzogInterpretation → Set
currentLiveInterpretations securityClassificationOnly = ⊤
currentLiveInterpretations authorityErasureCandidate = ⊤

observeCurrent :
  Element.MechanismRequirementKind →
  HerzogInterpretation →
  RequirementObservation
observeCurrent Element.requiresAuthorityMeaningErasure securityClassificationOnly = unsupported
observeCurrent Element.requiresAuthorityMeaningErasure authorityErasureCandidate = supported
observeCurrent Element.requiresOperationalPrerequisite securityClassificationOnly = unresolved
observeCurrent Element.requiresOperationalPrerequisite authorityErasureCandidate = unresolved
observeCurrent Element.requiresSameObjectProjectionPowerIncident securityClassificationOnly = unresolved
observeCurrent Element.requiresSameObjectProjectionPowerIncident authorityErasureCandidate = unresolved

data RequiredCurrent : Element.MechanismRequirementKind → Set where
  authorityMeaningRequired : RequiredCurrent Element.requiresAuthorityMeaningErasure
  powerPrerequisiteRequired : RequiredCurrent Element.requiresOperationalPrerequisite
  incidentWeldRequired : RequiredCurrent Element.requiresSameObjectProjectionPowerIncident

data RelevantCurrent : Element.MechanismRequirementKind → Set where
  authorityMeaningRelevant : RelevantCurrent Element.requiresAuthorityMeaningErasure
  powerPrerequisiteRelevant : RelevantCurrent Element.requiresOperationalPrerequisite
  incidentWeldRelevant : RelevantCurrent Element.requiresSameObjectProjectionPowerIncident

data AdmissibleCurrent : Element.MechanismRequirementKind → Set where
  authorityMeaningAdmissible : AdmissibleCurrent Element.requiresAuthorityMeaningErasure
  powerPrerequisiteAdmissible : AdmissibleCurrent Element.requiresOperationalPrerequisite
  incidentWeldAdmissible : AdmissibleCurrent Element.requiresSameObjectProjectionPowerIncident

currentProblem :
  Frontier.RequirementSalienceProblem
    Element.MechanismRequirementKind
    HerzogInterpretation
    RequirementObservation
currentProblem = Frontier.requirement-salience-problem
  currentLiveInterpretations
  observeCurrent
  RequiredCurrent
  RelevantCurrent
  AdmissibleCurrent
  "Current Herzog analytical fibre: authority-erasure interpretation is live against a security-classification-only interpretation; later mechanism coordinates remain unresolved in both."

currentAuthorityMeaningSplitsLiveFibre :
  Frontier.SalientRequirement
    currentProblem
    Element.requiresAuthorityMeaningErasure
currentAuthorityMeaningSplitsLiveFibre = Frontier.salient-requirement
  authorityMeaningRequired
  authorityMeaningRelevant
  authorityMeaningAdmissible
  (Frontier.splits-current-live-fibre
    securityClassificationOnly
    authorityErasureCandidate
    tt tt
    (λ ()))

powerPrerequisiteZeroCurrentDiscrimination :
  Frontier.ZeroCurrentDiscrimination
    currentProblem
    Element.requiresOperationalPrerequisite
powerPrerequisiteZeroCurrentDiscrimination = Frontier.zero-current-discrimination same
  where
    same : ∀ left right →
      currentLiveInterpretations left →
      currentLiveInterpretations right →
      observeCurrent Element.requiresOperationalPrerequisite left
      ≡ observeCurrent Element.requiresOperationalPrerequisite right
    same securityClassificationOnly securityClassificationOnly leftLive rightLive = refl
    same securityClassificationOnly authorityErasureCandidate leftLive rightLive = refl
    same authorityErasureCandidate securityClassificationOnly leftLive rightLive = refl
    same authorityErasureCandidate authorityErasureCandidate leftLive rightLive = refl

powerPrerequisiteStillRequiredButCurrentlyNonDiscriminating :
  Frontier.NecessaryButCurrentlyNonDiscriminating
    currentProblem
    Element.requiresOperationalPrerequisite
powerPrerequisiteStillRequiredButCurrentlyNonDiscriminating =
  Frontier.necessary-but-currently-nondiscriminating
    powerPrerequisiteRequired
    powerPrerequisiteRelevant
    powerPrerequisiteAdmissible
    powerPrerequisiteZeroCurrentDiscrimination

incidentWeldZeroCurrentDiscrimination :
  Frontier.ZeroCurrentDiscrimination
    currentProblem
    Element.requiresSameObjectProjectionPowerIncident
incidentWeldZeroCurrentDiscrimination = Frontier.zero-current-discrimination same
  where
    same : ∀ left right →
      currentLiveInterpretations left →
      currentLiveInterpretations right →
      observeCurrent Element.requiresSameObjectProjectionPowerIncident left
      ≡ observeCurrent Element.requiresSameObjectProjectionPowerIncident right
    same securityClassificationOnly securityClassificationOnly leftLive rightLive = refl
    same securityClassificationOnly authorityErasureCandidate leftLive rightLive = refl
    same authorityErasureCandidate securityClassificationOnly leftLive rightLive = refl
    same authorityErasureCandidate authorityErasureCandidate leftLive rightLive = refl

incidentWeldStillRequiredButCurrentlyNonDiscriminating :
  Frontier.NecessaryButCurrentlyNonDiscriminating
    currentProblem
    Element.requiresSameObjectProjectionPowerIncident
incidentWeldStillRequiredButCurrentlyNonDiscriminating =
  Frontier.necessary-but-currently-nondiscriminating
    incidentWeldRequired
    incidentWeldRelevant
    incidentWeldAdmissible
    incidentWeldZeroCurrentDiscrimination

------------------------------------------------------------------------
-- After authority meaning closes, the live fibre can change. A requirement that
-- was previously inert may become the next discriminator without having become
-- newly required.
------------------------------------------------------------------------

data AfterAuthorityInterpretation : Set where
  authorityErasureNoPowerNeed : AfterAuthorityInterpretation
  authorityErasurePowerNeed : AfterAuthorityInterpretation


afterAuthorityLive : AfterAuthorityInterpretation → Set
afterAuthorityLive authorityErasureNoPowerNeed = ⊤
afterAuthorityLive authorityErasurePowerNeed = ⊤

observeAfterAuthority :
  Element.MechanismRequirementKind →
  AfterAuthorityInterpretation →
  RequirementObservation
observeAfterAuthority Element.requiresAuthorityMeaningErasure authorityErasureNoPowerNeed = supported
observeAfterAuthority Element.requiresAuthorityMeaningErasure authorityErasurePowerNeed = supported
observeAfterAuthority Element.requiresOperationalPrerequisite authorityErasureNoPowerNeed = unsupported
observeAfterAuthority Element.requiresOperationalPrerequisite authorityErasurePowerNeed = supported
observeAfterAuthority Element.requiresSameObjectProjectionPowerIncident authorityErasureNoPowerNeed = unresolved
observeAfterAuthority Element.requiresSameObjectProjectionPowerIncident authorityErasurePowerNeed = unresolved

afterAuthorityProblem :
  Frontier.RequirementSalienceProblem
    Element.MechanismRequirementKind
    AfterAuthorityInterpretation
    RequirementObservation
afterAuthorityProblem = Frontier.requirement-salience-problem
  afterAuthorityLive
  observeAfterAuthority
  RequiredCurrent
  RelevantCurrent
  AdmissibleCurrent
  "After authority meaning closes, the remaining live interpretations collide on whether that erasure/subordination was actually prerequisite to the asserted operational power."

powerPrerequisiteBecomesSalientAfterAuthorityClosure :
  Frontier.SalientRequirement
    afterAuthorityProblem
    Element.requiresOperationalPrerequisite
powerPrerequisiteBecomesSalientAfterAuthorityClosure = Frontier.salient-requirement
  powerPrerequisiteRequired
  powerPrerequisiteRelevant
  powerPrerequisiteAdmissible
  (Frontier.splits-current-live-fibre
    authorityErasureNoPowerNeed
    authorityErasurePowerNeed
    tt tt
    (λ ()))

schedulerTransitionMatchesSalienceTransition :
  Scheduler.preferredDiscriminator Scheduler.operationalPrerequisiteOpen
  ≡ Scheduler.inspectPowerPrerequisite
schedulerTransitionMatchesSalienceTransition = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ZeroDiscriminationMeansNotRequired : Set where
data LaterSalienceMeansRequirementWasPreviouslyAbsent : Set where
data SalienceOrderIsLogicalEntailmentOrder : Set where

zeroDiscriminationDoesNotEraseLegalRequirement : ZeroDiscriminationMeansNotRequired → ⊥
zeroDiscriminationDoesNotEraseLegalRequirement ()

laterSalienceDoesNotCreateRequirementRetroactively :
  LaterSalienceMeansRequirementWasPreviouslyAbsent → ⊥
laterSalienceDoesNotCreateRequirementRetroactively ()

schedulerOrderIsNotEntailmentOrder : SalienceOrderIsLogicalEntailmentOrder → ⊥
schedulerOrderIsNotEntailmentOrder ()
