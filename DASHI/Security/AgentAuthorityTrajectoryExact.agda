module DASHI.Security.AgentAuthorityTrajectoryExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Core.Prelude using (⊥)

------------------------------------------------------------------------
-- Grounding and execution geometry.
--
-- This module deliberately separates:
--   proposal telemetry / public traces
-- from
--   grounded runtime evidence carrying authority consequences.
--
-- It mirrors the zkSEC/zkperf policy geometry without importing those
-- implementation repositories into the proof kernel.
------------------------------------------------------------------------

data GroundingState : Set where
  proposalOnly : GroundingState
  grounded : GroundingState

data Capability : Set where
  readCap : Capability
  writeCap : Capability
  executeCap : Capability
  networkEgressCap : Capability
  identityMutationCap : Capability
  policyMutationCap : Capability

data Channel : Set where
  localChannel : Channel
  selfChannel : Channel
  trustedPeerChannel : Channel
  publicChannel : Channel
  remoteAPIChannel : Channel

data Ring : Set where
  sovereignRing : Ring
  boundedRing : Ring
  remoteRing : Ring

data Transform : Set where
  classifyTransform : Transform
  ingestTransform : Transform
  readTransform : Transform
  reviewTransform : Transform
  probeTransform : Transform
  publishTransform : Transform
  executeTransform : Transform
  patchTransform : Transform

record ActionEnvelope : Set where
  constructor action-envelope
  field
    capability : Capability
    channel : Channel
    ring : Ring
    destination : String
    transform : Transform
    receiptRef : String

open ActionEnvelope public

record AuthorityPolicy : Set₁ where
  constructor authority-policy
  field
    capabilityAllowed : Capability → Set
    channelAllowed : Channel → Set
    ringAllowed : Ring → Set
    destinationAllowed : String → Set
    transformAllowed : Transform → Set
    receiptAuthorized : String → Set

open AuthorityPolicy public

record Admissible (policy : AuthorityPolicy) (action : ActionEnvelope) : Set where
  constructor admissible
  field
    capabilityOK : capabilityAllowed policy (capability action)
    channelOK : channelAllowed policy (channel action)
    ringOK : ringAllowed policy (ring action)
    destinationOK : destinationAllowed policy (destination action)
    transformOK : transformAllowed policy (transform action)
    receiptOK : receiptAuthorized policy (receiptRef action)

open Admissible public

record GroundedAction : Set where
  constructor grounded-action
  field
    action : ActionEnvelope
    groundingState : GroundingState
    groundingIsGrounded : groundingState ≡ grounded
    evidenceRef : String

open GroundedAction public

------------------------------------------------------------------------
-- Proposal-only observations cannot manufacture a GroundedAction.
------------------------------------------------------------------------

data ProposalTelemetry : Set where
  proposal-telemetry : String → ProposalTelemetry

record GroundedExecutionReceipt : Set where
  constructor grounded-execution-receipt
  field
    actionEvidence : GroundedAction
    runtimeReceiptRef : String

open GroundedExecutionReceipt public

------------------------------------------------------------------------
-- Core no-silent-authority-crossing theorem.
------------------------------------------------------------------------

groundedUnauthorizedExpansion :
  (policy : AuthorityPolicy) →
  (witness : GroundedAction) →
  (capabilityAllowed policy (capability (action witness)) → ⊥) →
  Admissible policy (action witness) →
  ⊥
groundedUnauthorizedExpansion policy witness capabilityDenied admission =
  capabilityDenied (capabilityOK admission)

groundedUnauthorizedDestination :
  (policy : AuthorityPolicy) →
  (witness : GroundedAction) →
  (destinationAllowed policy (destination (action witness)) → ⊥) →
  Admissible policy (action witness) →
  ⊥
groundedUnauthorizedDestination policy witness destinationDenied admission =
  destinationDenied (destinationOK admission)

groundedUnauthorizedTransform :
  (policy : AuthorityPolicy) →
  (witness : GroundedAction) →
  (transformAllowed policy (transform (action witness)) → ⊥) →
  Admissible policy (action witness) →
  ⊥
groundedUnauthorizedTransform policy witness transformDenied admission =
  transformDenied (transformOK admission)

------------------------------------------------------------------------
-- Trajectory-level first crossing.
------------------------------------------------------------------------

data All {A : Set} (P : A → Set) : List A → Set where
  all[] : All P []
  all∷ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

record FirstAuthorityCrossing (policy : AuthorityPolicy) : Set₁ where
  constructor first-authority-crossing
  field
    admissiblePrefix : List ActionEnvelope
    crossing : GroundedAction
    suffix : List ActionEnvelope
    prefixIsAdmissible : All (Admissible policy) admissiblePrefix
    crossingIsDenied : Admissible policy (action crossing) → ⊥

open FirstAuthorityCrossing public

firstAuthorityCrossingSound :
  (policy : AuthorityPolicy) →
  (crossingWitness : FirstAuthorityCrossing policy) →
  Admissible policy (action (crossing crossingWitness)) →
  ⊥
firstAuthorityCrossingSound policy crossingWitness =
  crossingIsDenied crossingWitness

------------------------------------------------------------------------
-- Knowledge acquisition is not authority acquisition.
--
-- External shared memory may widen what an agent knows.  It does not inhabit
-- the separate execution-authority type without an explicit receipt.
------------------------------------------------------------------------

record LearnedProcedure : Set where
  constructor learned-procedure
  field
    procedureRef : String

record ExecutionAuthority : Set where
  constructor execution-authority
  field
    authorizedReceiptRef : String
    authorizedCapability : Capability
    authorizedDestination : String

data KnowledgeIsAuthority : Set where

knowledgeIsNotAuthority : KnowledgeIsAuthority → ⊥
knowledgeIsNotAuthority ()

------------------------------------------------------------------------
-- ZK-ready trajectory commitments.
--
-- Hashes are abstract strings here: the formal claim is structural separation,
-- not a cryptographic implementation claim.
------------------------------------------------------------------------

record StepCommitment : Set where
  constructor step-commitment
  field
    priorCommitment : String
    actionCommitment : String
    observationCommitment : String
    receiptCommitment : String
    resultingCommitment : String

record ConformanceProofStatement (policy : AuthorityPolicy) : Set₁ where
  constructor conformance-proof-statement
  field
    committedAction : GroundedAction
    committedStep : StepCommitment
    admitted : Admissible policy (action committedAction)

record ViolationProofStatement (policy : AuthorityPolicy) : Set₁ where
  constructor violation-proof-statement
  field
    committedAction : GroundedAction
    committedStep : StepCommitment
    denied : Admissible policy (action committedAction) → ⊥
