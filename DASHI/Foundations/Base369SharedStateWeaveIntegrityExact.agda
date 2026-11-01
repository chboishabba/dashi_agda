module DASHI.Foundations.Base369SharedStateWeaveIntegrityExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- A relational calculation is woven into shared state only when participant
-- contributions, appraisal, provenance, unresolved boundaries and repair state
-- survive the update.  This module separates external event occurrence from
-- joint agreement, consultation from causal uptake, cessation from repair, and
-- process authorization from downstream obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

open import DASHI.Foundations.SSPTritCarrier using (SSPTrit; sspPosOne)
open import DASHI.Foundations.Base369CompletedRelationalDigitExact using
  (CompletionBit; uninstantiated; instantiated)
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube

data BoundaryStatus : Set where
  openBoundary deferredBoundary abandonedBySpeaker displacedUnrepaired
    resolvedBoundary : BoundaryStatus

record CalculationFibre : Set₁ where
  constructor calculationFibre
  field
    origin proposal path : Set
    interaction : Cube.OneRoundInteractionState
    openEnds : List BoundaryStatus
    completion : CompletionBit

open CalculationFibre public

record SharedState : Set₁ where
  constructor sharedState
  field
    currentObject contributionCarrier preferenceCarrier unresolvedCarrier : Set
    assentCarrier decisionProvenanceCarrier futureObligationCarrier : Set
    ruptureCarrier : Set

open SharedState public

record WeaveIntegrity
  (before : SharedState)
  (fibre : CalculationFibre)
  (after : SharedState) : Set₁ where
  constructor weaveIntegrity
  field
    contributionPreserved appraisalPreserved : Set
    outcomeAgreementSeparated decisionProvenancePreserved : Set
    openBoundariesPreserved noUnsupportedCarry repairCompletionWitnessed : Set

open WeaveIntegrity public

record ValidWeave : Set₁ where
  constructor validWeave
  field
    before : SharedState
    fibre : CalculationFibre
    after : SharedState
    integrity : WeaveIntegrity before fibre after

open ValidWeave public

record EventOccurred : Set where
  constructor eventOccurred
  field eventResult : SSPTrit

record JointAgreement : Set where
  constructor jointAgreement
  field
    assentA assentB : SSPTrit
    assentAIsPositive : assentA ≡ sspPosOne
    assentBIsPositive : assentB ≡ sspPosOne

-- There is intentionally no function EventOccurred -> JointAgreement.

record Consultation : Set₁ where
  constructor consultation
  field
    InputA InputB Decision : Set
    decide : InputA → InputB → Decision

open Consultation public

record CausallySensitiveConsultation (c : Consultation) : Set₁ where
  constructor causallySensitiveConsultation
  field changedInputCanChangeDecision : Set

record PseudoConsultation (c : Consultation) : Set₁ where
  constructor pseudoConsultation
  field
    inputSolicited : Set
    decisionInsensitiveToA : Set

record ActiveFibre : Set₁ where
  constructor activeFibre
  field
    object contribution : Set
    boundary : BoundaryStatus

open ActiveFibre public

record DisplacementEvent : Set₁ where
  constructor displacementEvent
  field
    interrupted : ActiveFibre
    replacementObject : Set
    interruptedMarkedDisplaced : boundary interrupted ≡ displacedUnrepaired

open DisplacementEvent public

record PreservedQueue : Set₁ where
  constructor preservedQueue
  field
    active deferred : List ActiveFibre

open PreservedQueue public

record RuptureState : Set where
  constructor ruptureState
  field
    activeConflict : Bool
    repairCompletion : CompletionBit

open RuptureState public

ceasedWithoutRepair : RuptureState
ceasedWithoutRepair = ruptureState false uninstantiated

completedRepair : RuptureState
completedRepair = ruptureState false instantiated

ceasedWithoutRepairIsNotCompleted :
  repairCompletion ceasedWithoutRepair ≡ uninstantiated
ceasedWithoutRepairIsNotCompleted = refl

completedRepairIsCompleted :
  repairCompletion completedRepair ≡ instantiated
completedRepairIsCompleted = refl

record ProcessAuthorization : Set₁ where
  constructor processAuthorization
  field
    Process : Set
    authorizedInitialAct : Process
    downstreamActs : List Process

open ProcessAuthorization public

record DownstreamCommitment (authorization : ProcessAuthorization) : Set₁ where
  constructor downstreamCommitment
  field
    committedAct : Process authorization
    explicitWitness : Set

record MemoryProjection : Set₁ where
  constructor memoryProjection
  field
    Source Narrative : Set
    project : Source → Narrative

open MemoryProjection public

record AgreementIntegrity (projection : MemoryProjection) : Set₁ where
  constructor agreementIntegrity
  field
    dissentNotErased unresolvedNotCompleted attributedAssentExcluded : Set

open AgreementIntegrity public
