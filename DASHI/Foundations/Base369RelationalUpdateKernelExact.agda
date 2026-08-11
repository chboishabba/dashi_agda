module DASHI.Foundations.Base369RelationalUpdateKernelExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Assemble the interaction cube, participant appraisal fibre, guarded
-- proposition response, shared-state weave and failure operators into one
-- reusable relational update kernel.  The kernel is asymmetric and
-- context-indexed: exchanging participants preserves only the structure for
-- which an explicit transport witness is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.Base369CalculationFibreClosureExact as Calculation
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.Base369PropositionResponseTransportExact as Response
import DASHI.Foundations.Base369RelationalFailureOperatorsExact as Failure
import DASHI.Foundations.Base369SharedStateWeaveIntegrityExact as Weave

record RelationalUpdateKernel : Set₁ where
  constructor relationalUpdateKernel
  field
    Participant : Set
    Environment : Set
    AuthorityContext : Set
    DependencyContext : Set
    CapacityContext : Set

    operator : Calculation.RelationalSheetOperator
    interaction : Cube.OneRoundInteractionState
    proposition : Response.PropositionNode
    episode : Response.DecisionEpisode
    sharedBefore : Weave.SharedState
    sharedAfter : Weave.SharedState

    authority : Participant → AuthorityContext
    dependency : Participant → DependencyContext
    capacity : Participant → CapacityContext

open RelationalUpdateKernel public

record ParticipantSwap (kernel : RelationalUpdateKernel) : Set₁ where
  constructor participantSwap
  field
    swap : Participant kernel → Participant kernel
    swapInvolutive : (p : Participant kernel) → swap (swap p) ≡ p

record OperatorEquivariance
  (kernel : RelationalUpdateKernel)
  (symmetry : ParticipantSwap kernel) : Set₁ where
  constructor operatorEquivariance
  field
    operatorTransportWitness : Set

record PropagationEquivariance
  (kernel : RelationalUpdateKernel)
  (symmetry : ParticipantSwap kernel) : Set₁ where
  constructor propagationEquivariance
  field
    authorityTransport : Set
    dependencyTransport : Set
    capacityTransport : Set
    weaveTransport : Set

-- Operator symmetry and propagation symmetry are independent.  Swapping A and
-- B may preserve the local calculation while failing to preserve the later
-- graph because authority, dependency, capacity or memory differ.

record KernelIntegrity (kernel : RelationalUpdateKernel) : Set₁ where
  constructor kernelIntegrity
  field
    exactResponseRequired : Set
    contributionEfficacyPreserved : Set
    outcomeNotPromotedToAgreement : Set
    complianceNotPromotedToConsent : Set
    openBoundariesRetained : Set
    repairRequiresCompletionWitness : Set
    descendantObligationsRequireTransport : Set
    priorContaminationExcluded : Set

open KernelIntegrity public
