module DASHI.Governance.GovernedArtifactCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Generic authority boundary.
--
-- Candidate generation is deliberately separated from canonical mutation.
-- A candidate may be computed and measured without acquiring authority.
-- Canonical mutation is witnessed only by the promoted constructor below.


data DiagnosticSeverity : Set where
  pass warn fail : DiagnosticSeverity

data Decision : Set where
  promote abstain reject : Decision

data SearchDecision : Set where
  admitToBeam discardFromBeam rejectTransition : SearchDecision

record CandidateEnvelope
  (State Policy Evidence Hash : Set) : Set where
  constructor candidateEnvelope
  field
    inputState        : State
    candidateState    : State
    effectivePolicy   : Policy
    candidateEvidence : Evidence
    inputHash         : Hash
    candidateHash     : Hash

open CandidateEnvelope public

record Receipt
  (State Policy Evidence Hash Warning Blocker : Set) : Set where
  constructor receipt
  field
    envelope   : CandidateEnvelope State Policy Evidence Hash
    severity   : DiagnosticSeverity
    warnings   : List Warning
    blockers   : List Blocker
    decision   : Decision
    policyHash : Hash
    receiptHash : Hash

open Receipt public

------------------------------------------------------------------------
-- The only constructors that select a resulting canonical state.


data SelectionWitness {State : Set}
  (current candidate result : State) : Decision → Set where
  promoteSelected : result ≡ candidate → SelectionWitness current candidate result promote
  abstainSelected : result ≡ current → SelectionWitness current candidate result abstain
  rejectSelected  : result ≡ current → SelectionWitness current candidate result reject

record GovernedOutcome
  (State Policy Evidence Hash Warning Blocker : Set)
  (current candidate : State) : Set where
  constructor governedOutcome
  field
    candidateReceipt : Receipt State Policy Evidence Hash Warning Blocker
    resultState      : State
    selection        : SelectionWitness current candidate resultState
      (Receipt.decision candidateReceipt)

open GovernedOutcome public

abstentionPreservesCanonical :
  ∀ {State Policy Evidence Hash Warning Blocker}
    {current candidate : State}
    (outcome : GovernedOutcome State Policy Evidence Hash Warning Blocker current candidate) →
    Receipt.decision (candidateReceipt outcome) ≡ abstain →
    resultState outcome ≡ current
abstentionPreservesCanonical
  (governedOutcome receipt result (abstainSelected proof)) refl = proof

rejectionPreservesCanonical :
  ∀ {State Policy Evidence Hash Warning Blocker}
    {current candidate : State}
    (outcome : GovernedOutcome State Policy Evidence Hash Warning Blocker current candidate) →
    Receipt.decision (candidateReceipt outcome) ≡ reject →
    resultState outcome ≡ current
rejectionPreservesCanonical
  (governedOutcome receipt result (rejectSelected proof)) refl = proof

promotionSelectsCandidate :
  ∀ {State Policy Evidence Hash Warning Blocker}
    {current candidate : State}
    (outcome : GovernedOutcome State Policy Evidence Hash Warning Blocker current candidate) →
    Receipt.decision (candidateReceipt outcome) ≡ promote →
    resultState outcome ≡ candidate
promotionSelectsCandidate
  (governedOutcome receipt result (promoteSelected proof)) refl = proof

------------------------------------------------------------------------
-- Warning evidence is carried independently of authorization.

record WarningPolicy (Warning : Set) : Set₁ where
  constructor warningPolicy
  field
    refinementAbstentionWarning : Warning → Set
    bodyAbstentionWarning       : Warning → Set
    rejectionWarning            : Warning → Set

open WarningPolicy public

record EvidenceAxes (Warning : Set) : Set where
  constructor evidenceAxes
  field
    diagnosticSeverity : DiagnosticSeverity
    warningEvidence    : List Warning
    authorization      : Decision

open EvidenceAxes public

record WarningCompatiblePromotion (Warning : Set) : Set where
  constructor warningCompatiblePromotion
  field
    retainedWarning        : Warning
    warningDecision        : Decision
    promotedDespiteWarning : warningDecision ≡ promote

------------------------------------------------------------------------
-- Hash-linked receipt composition.

record ReceiptLink (Hash : Set) : Set where
  constructor receiptLink
  field
    parentReceiptHash    : Hash
    consumedArtifactHash : Hash
    producedArtifactHash : Hash

open ReceiptLink public

record HashLinkedTransition
  (State Policy Evidence Hash Warning Blocker : Set) : Set where
  constructor hashLinkedTransition
  field
    transitionReceipt : Receipt State Policy Evidence Hash Warning Blocker
    lineage           : ReceiptLink Hash

open HashLinkedTransition public

------------------------------------------------------------------------
-- Consumer authority is proof-relevant and fail-closed.

record ConsumerAuthorization (Consumer : Set) : Set₁ where
  constructor consumerAuthorization
  field
    consumer        : Consumer
    carrierDecision : Decision
    carrierPromoted : carrierDecision ≡ promote
    notBlocked      : Set

open ConsumerAuthorization public

------------------------------------------------------------------------
-- Bounded search surface.  Beam admission is not production promotion.

record BoundedSearchPolicy (Hash : Set) : Set where
  constructor boundedSearchPolicy
  field
    generatorHash         : Hash
    backendSetHash        : Hash
    effectivePolicyHash   : Hash
    maximumDepth          : Nat
    beamWidth             : Nat
    deduplicationRuleHash : Hash
    tieBreakerHash        : Hash

open BoundedSearchPolicy public

record SearchTransition
  (State Operator Evidence Hash : Set) : Set where
  constructor searchTransition
  field
    parentState        : State
    operator           : Operator
    materializedChild  : State
    recomputedEvidence : Evidence
    parentStateHash    : Hash
    childStateHash     : Hash
    searchDecision     : SearchDecision
    productionDecision : Decision

open SearchTransition public

record BoundedNoPromotion
  (Hash : Set)
  (policy : BoundedSearchPolicy Hash) : Set₁ where
  constructor boundedNoPromotion
  field
    initialStateHash : Hash
    searchedStateCount : Nat
    noPromotedStateWithinDeclaredSearch : Set

open BoundedNoPromotion public

globalBasisExhaustionPromoted : Bool
globalBasisExhaustionPromoted = false

automaticCandidateMutationAuthority : Bool
automaticCandidateMutationAuthority = false
