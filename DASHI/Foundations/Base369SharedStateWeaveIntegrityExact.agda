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

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )
open import DASHI.Foundations.Base369CompletedRelationalDigitExact using
  ( CompletionBit
  ; uninstantiated
  ; instantiated
  )
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube

------------------------------------------------------------------------
-- Provenance-bearing calculation fibre.
------------------------------------------------------------------------

data BoundaryStatus : Set where
  openBoundary
  deferredBoundary
  abandonedBySpeaker
  displacedUnrepaired
  resolvedBoundary : BoundaryStatus

record CalculationFibre : Set where
  constructor calculationFibre
  field
    origin : Set
    proposal : Set
    path : Set
    interaction : Cube.OneRoundInteractionState
    openEnds : List BoundaryStatus
    completion : CompletionBit

open CalculationFibre public

------------------------------------------------------------------------
-- Shared conversational/process state.
------------------------------------------------------------------------

record SharedState : Set where
  constructor sharedState
  field
    currentObject : Set
    contributionCarrier : Set
    preferenceCarrier : Set
    unresolvedCarrier : Set
    assentCarrier : Set
    decisionProvenanceCarrier : Set
    futureObligationCarrier : Set
    ruptureCarrier : Set

open SharedState public

record WeaveIntegrity
  (before : SharedState)
  (fibre : CalculationFibre)
  (after : SharedState) : Set₁ where
  constructor weaveIntegrity
  field
    contributionPreserved : Set
    appraisalPreserved : Set
    outcomeAgreementSeparated : Set
    decisionProvenancePreserved : Set
    openBoundariesPreserved : Set
    noUnsupportedCarry : Set
    repairCompletionWitnessed : Set

open WeaveIntegrity public

record ValidWeave : Set₁ where
  constructor validWeave
  field
    before : SharedState
    fibre : CalculationFibre
    after : SharedState
    integrity : WeaveIntegrity before fibre after

open ValidWeave public

------------------------------------------------------------------------
-- Event occurrence does not imply agreement.
------------------------------------------------------------------------

record EventOccurred : Set where
  constructor eventOccurred
  field eventResult : SSPTrit

record JointAgreement : Set where
  constructor jointAgreement
  field
    assentA : SSPTrit
    assentB : SSPTrit
    assentAIsPositive : assentA ≡ sspPosOne
    assentBIsPositive : assentB ≡ sspPosOne

-- There is intentionally no function EventOccurred -> JointAgreement.

------------------------------------------------------------------------
-- Consultation sensitivity.
------------------------------------------------------------------------

record Consultation : Set₁ where
  constructor consultation
  field
    InputA : Set
    InputB : Set
    Decision : Set
    decide : InputA → InputB → Decision

open Consultation public

record CausallySensitiveConsultation (c : Consultation) : Set₁ where
  constructor causallySensitiveConsultation
  field
    changedInputCanChangeDecision : Set

record PseudoConsultation (c : Consultation) : Set₁ where
  constructor pseudoConsultation
  field
    inputSolicited : Set
    decisionInsensitiveToA : Set

-- A pseudo-consultation records an interface event without a causal-uptake
-- witness.  It cannot be promoted to joint decision by this module.

------------------------------------------------------------------------
-- Object displacement and queue preservation.
------------------------------------------------------------------------

record ActiveFibre : Set where
  constructor activeFibre
  field
    object : Set
    contribution : Set
    boundary : BoundaryStatus

open ActiveFibre public

record DisplacementEvent : Set where
  constructor displacementEvent
  field
    interrupted : ActiveFibre
    replacementObject : Set
    interruptedMarkedDisplaced :
      boundary interrupted ≡ displacedUnrepaired

open DisplacementEvent public

record PreservedQueue : Set where
  constructor preservedQueue
  field
    active : List ActiveFibre
    deferred : List ActiveFibre

open PreservedQueue public

------------------------------------------------------------------------
-- Cessation versus completed repair.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Future-capacity capture and process authorization.
------------------------------------------------------------------------

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

-- Authorization of the initial act does not construct DownstreamCommitment for
-- any descendant act.  A separate explicit witness is required.

------------------------------------------------------------------------
-- Retrospective compression must retain dissent and unresolved boundaries.
------------------------------------------------------------------------

record MemoryProjection : Set₁ where
  constructor memoryProjection
  field
    Source : Set
    Narrative : Set
    project : Source → Narrative

open MemoryProjection public

record AgreementIntegrity
  (projection : MemoryProjection) : Set₁ where
  constructor agreementIntegrity
  field
    dissentNotErased : Set
    unresolvedNotCompleted : Set
    attributedAssentExcluded : Set

open AgreementIntegrity public
