module DASHI.Cognition.PNF.TypedEventuallyConsistentFibreSystemExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_)

------------------------------------------------------------------------
-- Typed eventual consistency for PNF fibres.
--
-- This layer does not say that every transition commutes, and it does not
-- identify batching with semantics.  Each pair of fibres is explicitly typed
-- as one of three interaction modes:
--
--   commute : the two local advances may be reordered exactly;
--   join    : the two observations reconcile through an idempotent join;
--   braid   : order/provenance remains explicit and must be reconciled through
--             a directional residual obligation.
--
-- The runtime may batch only where the corresponding exact law is available.
------------------------------------------------------------------------

data InteractionMode : Set where
  commuteMode : InteractionMode
  joinMode : InteractionMode
  braidMode : InteractionMode

record JoinLaws (State : Set) : Set₁ where
  field
    merge : State → State → State
    mergeIdempotent : ∀ state → merge state state ≡ state
    mergeCommutative : ∀ left right → merge left right ≡ merge right left
    mergeAssociative : ∀ first second third →
      merge (merge first second) third ≡ merge first (merge second third)

open JoinLaws public

record TypedFibreDynamics
  (Fibre State Residual : Set)
  : Set₁ where
  field
    advance : Fibre → State → State
    interaction : Fibre → Fibre → InteractionMode
    joins : JoinLaws State

    braidResidual : Fibre → Fibre → State → Residual
    reconcileBraid : Fibre → Fibre → Residual → State → State

    independentCommutes :
      ∀ first second state →
      interaction first second ≡ commuteMode →
      advance first (advance second state)
        ≡ advance second (advance first state)

    joinReconciliationExact :
      ∀ first second state →
      interaction first second ≡ joinMode →
      advance first (advance second state)
        ≡ merge joins (advance first state) (advance second state)

open TypedFibreDynamics public

------------------------------------------------------------------------
-- Certified commuting batches.
--
-- A batch is a physical execution carrier.  Membership in one does not erase
-- individual fibre identity; the certificate merely proves that every pair in
-- the selected batch belongs to the exact commuting class.
------------------------------------------------------------------------

record CertifiedCommutingBatch
  {Fibre State Residual : Set}
  (Batch : Set)
  (dynamics : TypedFibreDynamics Fibre State Residual)
  : Set₁ where
  field
    member : Batch → Fibre → Set
    membersCommute :
      ∀ batch first second →
      member batch first →
      member batch second →
      interaction dynamics first second ≡ commuteMode

open CertifiedCommutingBatch public

certifiedBatchPairReorders :
  ∀ {Fibre State Residual Batch : Set}
    (dynamics : TypedFibreDynamics Fibre State Residual)
    (certificate : CertifiedCommutingBatch Batch dynamics)
    (batch : Batch)
    (first second : Fibre)
    (firstMember : member certificate batch first)
    (secondMember : member certificate batch second)
    (state : State) →
  advance dynamics first (advance dynamics second state)
    ≡ advance dynamics second (advance dynamics first state)
certifiedBatchPairReorders
  dynamics certificate batch first second firstMember secondMember state =
  independentCommutes dynamics first second state
    (membersCommute certificate batch first second firstMember secondMember)

------------------------------------------------------------------------
-- Explicit braid obligations.
--
-- A braid is not silently converted into a commutative join.  The residual is
-- carried together with the source/target fibre and the state that produced it.
------------------------------------------------------------------------

record BraidObligation
  {Fibre State Residual : Set}
  (dynamics : TypedFibreDynamics Fibre State Residual)
  : Set₁ where
  field
    source : Fibre
    target : Fibre
    state : State
    residual : Residual
    isBraided : interaction dynamics source target ≡ braidMode
    residualExact : residual ≡ braidResidual dynamics source target state

open BraidObligation public

reconcileExactBraid :
  ∀ {Fibre State Residual : Set}
    (dynamics : TypedFibreDynamics Fibre State Residual)
    (obligation : BraidObligation dynamics) →
  State
reconcileExactBraid dynamics obligation =
  reconcileBraid dynamics
    (source obligation)
    (target obligation)
    (residual obligation)
    (state obligation)

------------------------------------------------------------------------
-- Eventual fixed point / fairness boundary.
--
-- Local commute/join laws do not by themselves prove convergence.  A global
-- convergence claim therefore carries its schedule evaluator, fairness notion,
-- target fixed point, and the theorem that every fair schedule reaches it.
------------------------------------------------------------------------

record FairConvergenceCertificate
  {Fibre State Residual : Set}
  (Schedule : Set)
  (dynamics : TypedFibreDynamics Fibre State Residual)
  : Set₁ where
  field
    initial : State
    target : State
    evaluate : State → Schedule → State
    Fair : Schedule → Set

    targetLocallyStable : ∀ fibre → advance dynamics fibre target ≡ target
    fairSchedulesConverge :
      ∀ schedule → Fair schedule → evaluate initial schedule ≡ target

open FairConvergenceCertificate public

fairScheduleReachesFixedPoint :
  ∀ {Fibre State Residual Schedule : Set}
    (dynamics : TypedFibreDynamics Fibre State Residual)
    (certificate : FairConvergenceCertificate Schedule dynamics)
    (schedule : Schedule) →
    Fair certificate schedule →
  evaluate certificate (initial certificate) schedule ≡ target certificate
fairScheduleReachesFixedPoint dynamics certificate schedule fairness =
  fairSchedulesConverge certificate schedule fairness

------------------------------------------------------------------------
-- Orchestration economy.
--
-- Semantic fibres and physical queue operations are kept as different counts.
-- Batching is an optimisation only when it preserves semantic-fibre work while
-- reducing the physical orchestration coordinates.
------------------------------------------------------------------------

record OrchestrationReceipt : Set where
  field
    semanticFibres : Nat
    claimStatements : Nat
    lifecycleStatements : Nat
    transactionBoundaries : Nat

open OrchestrationReceipt public

record OrchestrationNonWorsening
  (before after : OrchestrationReceipt)
  : Set where
  field
    sameSemanticFibres : semanticFibres after ≡ semanticFibres before
    claimsNonWorse : claimStatements after ≤ᶜ claimStatements before
    lifecycleNonWorse : lifecycleStatements after ≤ᶜ lifecycleStatements before
    transactionsNonWorse :
      transactionBoundaries after ≤ᶜ transactionBoundaries before

open OrchestrationNonWorsening public
