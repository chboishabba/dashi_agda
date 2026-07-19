module DASHI.Governance.CaseyITIRNixBridge where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Casey / ITIR / SensibLaw / StatiBaker / Nix bridge.
--
-- This file separates four authorities:
--
--   * Casey candidate state grows monotonically by semilattice join;
--   * governance emits resolution receipts rather than deleting history;
--   * an active view is derived from state plus receipts;
--   * Nix-like materialization consumes only a frozen BuildView.
--
-- The development is generic: concrete file versions, paths, receipts,
-- hashes, gap values, and artifacts are supplied by an implementation.
-- No claim that every governance process is contractive is made.  A
-- contraction witness is an explicit obligation of a concrete instance.

------------------------------------------------------------------------
-- Replicated candidate substrate.

record JoinSemilattice
  {ℓ : Level}
  (A : Set ℓ)
  : Set ℓ where
  field
    _⊔_ : A → A → A

    ⊔-associative :
      ∀ x y z →
      (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)

    ⊔-commutative :
      ∀ x y →
      x ⊔ y ≡ y ⊔ x

    ⊔-idempotent :
      ∀ x →
      x ⊔ x ≡ x

open JoinSemilattice public

record CaseySubstrate
  {sℓ : Level}
  : Set (Level.suc sℓ) where
  field
    State : Set sℓ
    stateJoin : JoinSemilattice State

open CaseySubstrate public

module Replication
  {sℓ : Level}
  (K : CaseySubstrate {sℓ})
  where

  open JoinSemilattice (stateJoin K)

  merge : State K → State K → State K
  merge = _⊔_

  merge-associative :
    ∀ x y z →
    merge (merge x y) z ≡ merge x (merge y z)
  merge-associative = ⊔-associative

  merge-commutative :
    ∀ x y →
    merge x y ≡ merge y x
  merge-commutative = ⊔-commutative

  merge-idempotent :
    ∀ x →
    merge x x ≡ x
  merge-idempotent = ⊔-idempotent

------------------------------------------------------------------------
-- Receipt-based governance.
--
-- A resolution does not destructively replace the candidate graph.  It is
-- appended as a receipt, and policy derives an active workspace view from
-- the monotone state plus the monotone receipt state.

record GovernanceLayer
  {sℓ rℓ vℓ pℓ : Level}
  (K : CaseySubstrate {sℓ})
  : Set (Level.suc (sℓ ⊔ rℓ ⊔ vℓ ⊔ pℓ)) where
  field
    ReceiptState : Set rℓ
    receiptJoin : JoinSemilattice ReceiptState

    ActiveView : Set vℓ
    Proposal : Set pℓ

    propose : State K → Proposal
    emitResolution : State K → ReceiptState → Proposal → ReceiptState
    activeView : State K → ReceiptState → ActiveView

open GovernanceLayer public

------------------------------------------------------------------------
-- Frozen build worlds and deterministic materialization.

record BuildBoundary
  {sℓ rℓ vℓ pℓ bℓ aℓ : Level}
  (K : CaseySubstrate {sℓ})
  (G : GovernanceLayer {rℓ = rℓ} {vℓ = vℓ} {pℓ = pℓ} K)
  : Set (Level.suc (sℓ ⊔ rℓ ⊔ vℓ ⊔ pℓ ⊔ bℓ ⊔ aℓ)) where
  field
    BuildView : Set bℓ
    Artifact : Set aℓ

    freeze :
      State K →
      ReceiptState G →
      ActiveView G →
      BuildView

    -- Nix belongs here: after selection has been frozen, never on the
    -- unresolved candidate state directly.
    nixMaterialize : BuildView → Artifact

open BuildBoundary public

module Materialization
  {sℓ rℓ vℓ pℓ bℓ aℓ : Level}
  (K : CaseySubstrate {sℓ})
  (G : GovernanceLayer {rℓ = rℓ} {vℓ = vℓ} {pℓ = pℓ} K)
  (B : BuildBoundary {bℓ = bℓ} {aℓ = aℓ} K G)
  where

  materialize :
    State K →
    ReceiptState G →
    ActiveView G →
    Artifact B
  materialize state receipts view =
    nixMaterialize B (freeze B state receipts view)

  same-build-view-same-artifact :
    ∀ {x y : BuildView B} →
    x ≡ y →
    nixMaterialize B x ≡ nixMaterialize B y
  same-build-view-same-artifact = cong (nixMaterialize B)

------------------------------------------------------------------------
-- The O, R, C, S, L, P, G, F institutional schema.
--
-- L is represented here by the join-semilattice structure carried by S,
-- rather than by an unstructured ontology label.  C computes proposals;
-- G emits adjudication receipts and derives the effective view; F measures
-- unresolved divergence or another implementation-selected gap.

record InstitutionalModel
  {oℓ qℓ sℓ rℓ vℓ pℓ fℓ bℓ aℓ : Level}
  : Set (Level.suc (oℓ ⊔ qℓ ⊔ sℓ ⊔ rℓ ⊔ vℓ ⊔ pℓ ⊔ fℓ ⊔ bℓ ⊔ aℓ)) where
  field
    O-Organization : Set oℓ
    R-Requirement : Set qℓ

    casey : CaseySubstrate {sℓ}
    governance :
      GovernanceLayer {rℓ = rℓ} {vℓ = vℓ} {pℓ = pℓ} casey
    buildBoundary :
      BuildBoundary {bℓ = bℓ} {aℓ = aℓ} casey governance

    -- C: requirement-indexed proposal computation.
    C-Code :
      O-Organization →
      R-Requirement →
      State casey →
      Proposal governance

    -- F: gap carrier and comparison relation.  No numeric authority is
    -- assumed; concrete systems may use candidate multiplicity, entropy,
    -- policy debt, failed builds, or a product of these.
    Gap : Set fℓ
    _≤F_ : Gap → Gap → Set fℓ
    F-Gap :
      State casey →
      ReceiptState governance →
      Gap

open InstitutionalModel public

------------------------------------------------------------------------
-- One proof-carrying governance cycle.

record GovernanceCycle
  {oℓ qℓ sℓ rℓ vℓ pℓ fℓ bℓ aℓ : Level}
  (M : InstitutionalModel
    {oℓ} {qℓ} {sℓ} {rℓ} {vℓ} {pℓ} {fℓ} {bℓ} {aℓ})
  : Set (oℓ ⊔ qℓ ⊔ sℓ ⊔ rℓ ⊔ vℓ ⊔ pℓ ⊔ fℓ) where
  field
    organization : O-Organization M
    requirement : R-Requirement M
    stateBefore : State (casey M)
    receiptsBefore : ReceiptState (governance M)

    proposal : Proposal (governance M)
    proposalIsComputed :
      proposal ≡
      C-Code M organization requirement stateBefore

    receiptsAfter : ReceiptState (governance M)
    receiptsAreEmitted :
      receiptsAfter ≡
      emitResolution
        (governance M)
        stateBefore
        receiptsBefore
        proposal

    gapDoesNotIncrease :
      _≤F_ M
        (F-Gap M stateBefore receiptsAfter)
        (F-Gap M stateBefore receiptsBefore)

open GovernanceCycle public

------------------------------------------------------------------------
-- Explicit contraction obligation.
--
-- This record is deliberately stronger than mere non-increase.  A concrete
-- metric/ultrametric implementation supplies StrictlyBelow and proves that
-- every admissible unresolved cycle strictly reduces its gap.  Fixed-point
-- or Banach-style conclusions require additional completeness and metric
-- hypotheses and are therefore not asserted by this bridge alone.

record ContractionWitness
  {oℓ qℓ sℓ rℓ vℓ pℓ fℓ bℓ aℓ : Level}
  (M : InstitutionalModel
    {oℓ} {qℓ} {sℓ} {rℓ} {vℓ} {pℓ} {fℓ} {bℓ} {aℓ})
  : Set (Level.suc (oℓ ⊔ qℓ ⊔ sℓ ⊔ rℓ ⊔ vℓ ⊔ pℓ ⊔ fℓ)) where
  field
    Resolved :
      State (casey M) →
      ReceiptState (governance M) →
      Set fℓ

    StrictlyBelow : Gap M → Gap M → Set fℓ

    admissible-cycle-contracts :
      (cycle : GovernanceCycle M) →
      Resolved cycle.stateBefore cycle.receiptsBefore →
      StrictlyBelow
        (F-Gap M cycle.stateBefore cycle.receiptsAfter)
        (F-Gap M cycle.stateBefore cycle.receiptsBefore)

open ContractionWitness public

------------------------------------------------------------------------
-- StatiBaker-style observer boundary.
--
-- The observer receives immutable references/receipts, not mutable Casey
-- candidate authority.  This prevents the provenance ledger from silently
-- becoming the canonical superposition store.

record ObserverBoundary
  {sℓ rℓ vℓ pℓ refℓ : Level}
  (K : CaseySubstrate {sℓ})
  (G : GovernanceLayer {rℓ = rℓ} {vℓ = vℓ} {pℓ = pℓ} K)
  : Set (Level.suc (sℓ ⊔ rℓ ⊔ vℓ ⊔ pℓ ⊔ refℓ)) where
  field
    ImmutableReference : Set refℓ

    stateReference : State K → ImmutableReference
    receiptReference : ReceiptState G → ImmutableReference
    activeViewReference : ActiveView G → ImmutableReference

open ObserverBoundary public
