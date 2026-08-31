module DASHI.Reasoning.Spacy369CriticalAuditOptionConeHistoryExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Reasoning.Spacy369CriticalAuditDiscriminatorPlannerExact as Planner
import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer

------------------------------------------------------------------------
-- INFORMATION-ACTION OPTION CONES + HISTORY NON-FACTORABILITY
--
-- Structural reuse only: `Available` means an admissible next information
-- action for the declared analysis objective.  It does not mean social freedom,
-- welfare, coercion, or physical reachability.  Removing an irrelevant probe
-- after a consumer closes is computational pruning, not harm.
------------------------------------------------------------------------

data AnalysisObjective : Set where
  operationalOnly
  scopeSensitive
  subjectPositionSensitive
  broadCriticalAudit
  : AnalysisObjective

data InformationAction : Set where
  terminateWithOperationalDecision
  askScopeQuestion
  acquireSubjectPosition
  inspectClosureResidual
  inspectReciprocalRelation
  : InformationAction

data InformationAvailable : AnalysisObjective → InformationAction → Set where
  operationalStop :
    InformationAvailable operationalOnly terminateWithOperationalDecision

  scopeQuestion :
    InformationAvailable scopeSensitive askScopeQuestion

  subjectQuestion :
    InformationAvailable subjectPositionSensitive acquireSubjectPosition

  broadStop :
    InformationAvailable broadCriticalAudit terminateWithOperationalDecision
  broadScope :
    InformationAvailable broadCriticalAudit askScopeQuestion
  broadSubject :
    InformationAvailable broadCriticalAudit acquireSubjectPosition
  broadClosure :
    InformationAvailable broadCriticalAudit inspectClosureResidual
  broadReciprocal :
    InformationAvailable broadCriticalAudit inspectReciprocalRelation

informationOptionCone : Cone.SafeReachabilitySystem AnalysisObjective InformationAction
informationOptionCone = Cone.safeReachabilitySystem InformationAvailable

operationalOptionsIncludedInBroad :
  (option : InformationAction) →
  InformationAvailable operationalOnly option →
  InformationAvailable broadCriticalAudit option
operationalOptionsIncludedInBroad terminateWithOperationalDecision operationalStop = broadStop

broadToOperationalPrunesScopeProbe :
  Cone.StrictSafeReachabilityContraction
    informationOptionCone broadCriticalAudit operationalOnly
broadToOperationalPrunesScopeProbe =
  Cone.strictSafeReachabilityContraction
    operationalOptionsIncludedInBroad
    askScopeQuestion
    broadScope
    (λ ())

scopeProbeAvailableForScopeConsumer :
  InformationAvailable scopeSensitive askScopeQuestion
scopeProbeAvailableForScopeConsumer = scopeQuestion

subjectProbeAvailableForSubjectConsumer :
  InformationAvailable subjectPositionSensitive acquireSubjectPosition
subjectProbeAvailableForSubjectConsumer = subjectQuestion

scopeConsumerDoesNotExposeSubjectProbe :
  InformationAvailable scopeSensitive acquireSubjectPosition → ⊥
scopeConsumerDoesNotExposeSubjectProbe ()

subjectConsumerDoesNotExposeScopeProbe :
  InformationAvailable subjectPositionSensitive askScopeQuestion → ⊥
subjectConsumerDoesNotExposeScopeProbe ()

------------------------------------------------------------------------
-- Distinct audit routes may reconverge on the same operational endpoint while
-- retaining different path residue.
------------------------------------------------------------------------

data AuditHistory : Set where
  directOperationalClosure
  scopeAuditThenOperationalClosure
  subjectAuditThenOperationalClosure
  : AuditHistory

operationalEndpoint : AuditHistory → Consumer.OperationalDecision
operationalEndpoint directOperationalClosure = Consumer.noAutomaticStateMutation
operationalEndpoint scopeAuditThenOperationalClosure = Consumer.noAutomaticStateMutation
operationalEndpoint subjectAuditThenOperationalClosure = Consumer.noAutomaticStateMutation

data AuditRouteResidue : Set where
  noAuditResidue
  scopeAuditResidue
  subjectAuditResidue
  : AuditRouteResidue

auditResidue : AuditHistory → AuditRouteResidue
auditResidue directOperationalClosure = noAuditResidue
auditResidue scopeAuditThenOperationalClosure = scopeAuditResidue
auditResidue subjectAuditThenOperationalClosure = subjectAuditResidue

scopeResidueDiffersFromSubjectResidue :
  auditResidue scopeAuditThenOperationalClosure
  ≡ auditResidue subjectAuditThenOperationalClosure → ⊥
scopeResidueDiffersFromSubjectResidue ()

sameOperationalEndpointAcrossAuditHistories :
  operationalEndpoint scopeAuditThenOperationalClosure
  ≡ operationalEndpoint subjectAuditThenOperationalClosure
sameOperationalEndpointAcrossAuditHistories = refl

operationalEndpointCannotRecoverAuditResidue :
  INF.FactorsThrough operationalEndpoint auditResidue → ⊥
operationalEndpointCannotRecoverAuditResidue =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      scopeAuditThenOperationalClosure
      subjectAuditThenOperationalClosure
      refl
      scopeResidueDiffersFromSubjectResidue)

------------------------------------------------------------------------
-- Materialised planner anchors.
------------------------------------------------------------------------

materialisedOperationalPlan = Planner.operationalSequentialPlan
materialisedScopePlan = Planner.scopeSequentialPlan
materialisedSubjectPlan = Planner.subjectSequentialPlan

record Spacy369CriticalAuditOptionConeHistoryBoundary : Set where
  constructor spacy369CriticalAuditOptionConeHistoryBoundary
  field
    consumerChoiceCanChangeAvailableInformationActions : Bool
    consumerChoiceCanChangeAvailableInformationActionsIsTrue :
      consumerChoiceCanChangeAvailableInformationActions ≡ true
    closedOperationalObjectiveRetainsEveryCriticalProbe : Bool
    closedOperationalObjectiveRetainsEveryCriticalProbeIsFalse :
      closedOperationalObjectiveRetainsEveryCriticalProbe ≡ false
    pruningIrrelevantProbeIsSocialCoercionClaim : Bool
    pruningIrrelevantProbeIsSocialCoercionClaimIsFalse :
      pruningIrrelevantProbeIsSocialCoercionClaim ≡ false
    sameOperationalEndpointRecoversAuditHistory : Bool
    sameOperationalEndpointRecoversAuditHistoryIsFalse :
      sameOperationalEndpointRecoversAuditHistory ≡ false
    sameOperationalEndpointErasesAuditResidue : Bool
    sameOperationalEndpointErasesAuditResidueIsFalse :
      sameOperationalEndpointErasesAuditResidue ≡ false
    optionConeComparisonClaimsActualHistoricalTransition : Bool
    optionConeComparisonClaimsActualHistoricalTransitionIsFalse :
      optionConeComparisonClaimsActualHistoricalTransition ≡ false

canonicalSpacy369CriticalAuditOptionConeHistoryBoundary :
  Spacy369CriticalAuditOptionConeHistoryBoundary
canonicalSpacy369CriticalAuditOptionConeHistoryBoundary =
  spacy369CriticalAuditOptionConeHistoryBoundary
    true refl false refl false refl false refl false refl false refl
