module DASHI.Cognition.PNF.SensibLawWrongTypeLiveResidualSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual

------------------------------------------------------------------------
-- LIVE LEGAL RESIDUAL SCHEDULER
--
-- Cross-pollination of the live-hypothesis scheduler geometry into SensibLaw.
-- The next legal/source move is indexed by the CURRENT residual, consumer and
-- authority surface. Historical usefulness does not imply present salience.
--
-- This owner reuses the existing cross-domain residual-move vocabulary: source
-- recovery, context audit and proof search remain distinct move kinds.
------------------------------------------------------------------------

data LegalLiveResidual : Set where
  authorityMeaningOpen
  operationalPrerequisiteOpen
  sameObjectIncidentWeldOpen
  applicabilityOpen
  violationOpen
  liabilityRemedyOpen
  consumerActionClosed
  : LegalLiveResidual

data LegalDiscriminator : Set where
  recoverAuthorityMeaningEvidence
  inspectPowerPrerequisite
  recoverIncidentWeldEvidence
  proveApplicability
  proveViolation
  inspectLiabilityRemedy
  stopForConsumer
  : LegalDiscriminator

preferredDiscriminator : LegalLiveResidual → LegalDiscriminator
preferredDiscriminator authorityMeaningOpen = recoverAuthorityMeaningEvidence
preferredDiscriminator operationalPrerequisiteOpen = inspectPowerPrerequisite
preferredDiscriminator sameObjectIncidentWeldOpen = recoverIncidentWeldEvidence
preferredDiscriminator applicabilityOpen = proveApplicability
preferredDiscriminator violationOpen = proveViolation
preferredDiscriminator liabilityRemedyOpen = inspectLiabilityRemedy
preferredDiscriminator consumerActionClosed = stopForConsumer

moveKind : LegalDiscriminator → Costed.ResidualInformationMoveKind
moveKind recoverAuthorityMeaningEvidence = Costed.sourceRecoveryResidualMove
moveKind inspectPowerPrerequisite = Costed.contextAuditResidualMove
moveKind recoverIncidentWeldEvidence = Costed.sourceRecoveryResidualMove
moveKind proveApplicability = Costed.proofSearchResidualMove
moveKind proveViolation = Costed.proofSearchResidualMove
moveKind inspectLiabilityRemedy = Costed.contextAuditResidualMove
moveKind stopForConsumer = Costed.contextAuditResidualMove

residualKind : LegalLiveResidual → Residual.LegalResidualKind
residualKind authorityMeaningOpen = Residual.missingRelationalFeature
residualKind operationalPrerequisiteOpen = Residual.missingInstitutionalConstraint
residualKind sameObjectIncidentWeldOpen = Residual.missingFactualFeature
residualKind applicabilityOpen = Residual.missingJurisdiction
residualKind violationOpen = Residual.missingDoctrinalPredicate
residualKind liabilityRemedyOpen = Residual.missingRemedyExecution
residualKind consumerActionClosed = Residual.missingCommunityOutcome

------------------------------------------------------------------------
-- Portfolio coordinates. These are declared/certified coordinates, not a hidden
-- probability model. Authority remains independent from gain and relevance.
------------------------------------------------------------------------

record LegalMoveAssessment : Set where
  constructor legalMoveAssessment
  field
    discriminator : LegalDiscriminator
    cost : Nat
    certifiedGain : Nat
    consumerRelevant : Bool
    authorityAdmissible : Bool
    assessmentReference : String

open LegalMoveAssessment public

authorityMeaningAssessment : LegalMoveAssessment
authorityMeaningAssessment = legalMoveAssessment
  recoverAuthorityMeaningEvidence 2 3 true true
  "Current analytical consumer is blocked on before/after authority-meaning evidence."

powerPrerequisiteAssessment : LegalMoveAssessment
powerPrerequisiteAssessment = legalMoveAssessment
  inspectPowerPrerequisite 3 2 true true
  "Current analytical consumer is blocked on the rule/power prerequisite rather than additional classification repetition."

incidentWeldAssessment : LegalMoveAssessment
incidentWeldAssessment = legalMoveAssessment
  recoverIncidentWeldEvidence 4 3 true true
  "Exact classification -> order -> unit -> tactic -> incident lineage remains open."

inadmissibleBroadFishingAssessment : LegalMoveAssessment
inadmissibleBroadFishingAssessment = legalMoveAssessment
  recoverIncidentWeldEvidence 1 5 true false
  "Nominally high-gain broad acquisition without a declared authority/provenance basis is not executable."

------------------------------------------------------------------------
-- Finite Pareto surface. We keep the comparison division-free and probability-
-- free, matching CostedResidualInformationChoiceExact.
------------------------------------------------------------------------

data LegalParetoRelation : LegalMoveAssessment → LegalMoveAssessment → Set where
  legalParetoDominates :
    ∀ {left right} →
    cost left ≤ cost right →
    certifiedGain right ≤ certifiedGain left →
    consumerRelevant left ≡ true →
    authorityAdmissible left ≡ true →
    LegalParetoRelation left right

record LegalParetoChoice (selected : LegalMoveAssessment) : Set where
  constructor legalParetoChoice
  field
    selectedRelevant : consumerRelevant selected ≡ true
    selectedAdmissible : authorityAdmissible selected ≡ true
    comparisonReference : String

open LegalParetoChoice public

currentAuthorityMeaningChoice : LegalParetoChoice authorityMeaningAssessment
currentAuthorityMeaningChoice = legalParetoChoice refl refl
  "Selected on the current authority-meaning residual; cost/gain do not override admissibility."

------------------------------------------------------------------------
-- Executable finite Pareto check over the declared current alternatives.
------------------------------------------------------------------------

_&&_ : Bool → Bool → Bool
false && right = false
true && right = right

not : Bool → Bool
not false = true
not true = false

_≤ᵇ_ : Nat → Nat → Bool
zero ≤ᵇ right = true
suc left ≤ᵇ zero = false
suc left ≤ᵇ suc right = left ≤ᵇ right

dominates? : LegalMoveAssessment → LegalMoveAssessment → Bool
dominates? left right =
  consumerRelevant left &&
  (authorityAdmissible left &&
  ((cost left ≤ᵇ cost right) &&
   (certifiedGain right ≤ᵇ certifiedGain left)))

strictlyDominates? : LegalMoveAssessment → LegalMoveAssessment → Bool
strictlyDominates? left right =
  dominates? left right && not (dominates? right left)

undominatedAgainst? : LegalMoveAssessment → LegalMoveAssessment → Bool
undominatedAgainst? selected alternative =
  not (strictlyDominates? alternative selected)

currentAuthorityMeaningParetoUndominated : Bool
currentAuthorityMeaningParetoUndominated =
  undominatedAgainst? authorityMeaningAssessment powerPrerequisiteAssessment &&
  (undominatedAgainst? authorityMeaningAssessment incidentWeldAssessment &&
   undominatedAgainst? authorityMeaningAssessment inadmissibleBroadFishingAssessment)

currentAuthorityMeaningParetoUndominatedIsTrue :
  currentAuthorityMeaningParetoUndominated ≡ true
currentAuthorityMeaningParetoUndominatedIsTrue = refl

inadmissibleNominalGainDoesNotDominate :
  dominates? inadmissibleBroadFishingAssessment authorityMeaningAssessment ≡ false
inadmissibleNominalGainDoesNotDominate = refl

authorityMeaningDominatesCostlyPowerProbeAtCurrentCoordinates :
  dominates? authorityMeaningAssessment powerPrerequisiteAssessment ≡ true
authorityMeaningDominatesCostlyPowerProbeAtCurrentCoordinates = refl

------------------------------------------------------------------------
-- State-dependent portfolio update.
------------------------------------------------------------------------

afterAuthorityMeaningCloses : LegalLiveResidual
afterAuthorityMeaningCloses = operationalPrerequisiteOpen

portfolioChangesAfterAuthorityMeaningClosure :
  preferredDiscriminator authorityMeaningOpen
  ≡ recoverAuthorityMeaningEvidence
portfolioChangesAfterAuthorityMeaningClosure = refl

afterClosureSelectsPowerAudit :
  preferredDiscriminator afterAuthorityMeaningCloses
  ≡ inspectPowerPrerequisite
afterClosureSelectsPowerAudit = refl

sourceRecoveryNotAlwaysNext :
  preferredDiscriminator afterAuthorityMeaningCloses
  ≡ inspectPowerPrerequisite
sourceRecoveryNotAlwaysNext = refl

------------------------------------------------------------------------
-- Action-fibre stopping seam.
--
-- Legal epistemic closure for a declared consumer does not require unique world,
-- motive or historical-mechanism identity. But stop authority is independent.
------------------------------------------------------------------------

record LegalActionFibreClosure : Set where
  constructor legalActionFibreClosure
  field
    liveAlternativesRemain : Bool
    liveAlternativesRemainIsTrue : liveAlternativesRemain ≡ true
    allLiveAlternativesInduceSameConsumerAction : Bool
    allLiveAlternativesInduceSameConsumerActionIsTrue :
      allLiveAlternativesInduceSameConsumerAction ≡ true
    actionAuthorityRecovered : Bool
    stopPermitted : Bool
    stopPermittedOnlyWithAuthority :
      actionAuthorityRecovered ≡ true → stopPermitted ≡ true

open LegalActionFibreClosure public

authorisedLegalStop : LegalActionFibreClosure
authorisedLegalStop = legalActionFibreClosure true refl true refl true true (λ _ → refl)

unauthorisedAgreementDoesNotStop : LegalActionFibreClosure
unauthorisedAgreementDoesNotStop = legalActionFibreClosure true refl true refl false false (λ ())

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LargestGainAlwaysSelected : Set where
data CheapestMoveAlwaysSelected : Set where
data OnceUsefulLegalProbeAlwaysUseful : Set where
data RetainedLegalEvidenceRequiresRepeatAcquisition : Set where
data ActionAgreementCreatesAuthority : Set where
data ConsumerClosureMeansUniqueHistoricalMechanism : Set where

largestGainNeedsAdmissibility : LargestGainAlwaysSelected → ⊥
largestGainNeedsAdmissibility ()

cheapestNeedsRelevanceAndGain : CheapestMoveAlwaysSelected → ⊥
cheapestNeedsRelevanceAndGain ()

historicalUsefulnessDoesNotFreezePortfolio : OnceUsefulLegalProbeAlwaysUseful → ⊥
historicalUsefulnessDoesNotFreezePortfolio ()

retentionDoesNotRequireRepeat : RetainedLegalEvidenceRequiresRepeatAcquisition → ⊥
retentionDoesNotRequireRepeat ()

actionAgreementDoesNotCreateAuthority : ActionAgreementCreatesAuthority → ⊥
actionAgreementDoesNotCreateAuthority ()

consumerClosureDoesNotIdentifyHistory : ConsumerClosureMeansUniqueHistoricalMechanism → ⊥
consumerClosureDoesNotIdentifyHistory ()
