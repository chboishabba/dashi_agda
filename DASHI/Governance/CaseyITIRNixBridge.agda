module DASHI.Governance.CaseyITIRNixBridge where

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _⊔ℓ_)
open import Agda.Builtin.Equality using (_≡_; refl)

cong :
  ∀ {a b : Level} {A : Set a} {B : Set b} →
  (f : A → B) →
  ∀ {x y} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Casey / ITIR / SensibLaw / StatiBaker / Nix bridge.
--
-- Four authorities are separated:
--
--   * Casey candidate state grows monotonically by semilattice join;
--   * governance emits receipts rather than deleting candidate history;
--   * policy derives an active view from state plus receipts;
--   * Nix-like materialization consumes only a frozen BuildView.
--
-- Concrete file versions, paths, hashes, gap values, and artifacts are
-- supplied by an implementation.  Contractivity is an explicit obligation,
-- not a broad claim about every governance process.

record JoinSemilattice
  {ℓ : Level}
  (A : Set ℓ)
  : Set ℓ where
  field
    join : A → A → A

    join-associative :
      ∀ x y z →
      join (join x y) z ≡ join x (join y z)

    join-commutative :
      ∀ x y →
      join x y ≡ join y x

    join-idempotent :
      ∀ x →
      join x x ≡ x

open JoinSemilattice public

record CaseySubstrate
  {sℓ : Level}
  : Set (lsuc sℓ) where
  field
    State : Set sℓ
    stateJoin : JoinSemilattice State

open CaseySubstrate public

module Replication
  {sℓ : Level}
  (K : CaseySubstrate {sℓ})
  where

  private
    semilattice = stateJoin K

  merge : State K → State K → State K
  merge = JoinSemilattice.join semilattice

  merge-associative :
    ∀ x y z →
    merge (merge x y) z ≡ merge x (merge y z)
  merge-associative = JoinSemilattice.join-associative semilattice

  merge-commutative :
    ∀ x y →
    merge x y ≡ merge y x
  merge-commutative = JoinSemilattice.join-commutative semilattice

  merge-idempotent :
    ∀ x →
    merge x x ≡ x
  merge-idempotent = JoinSemilattice.join-idempotent semilattice

------------------------------------------------------------------------
-- Receipt-based governance.

record GovernanceLayer
  {sℓ rℓ vℓ pℓ : Level}
  (K : CaseySubstrate {sℓ})
  : Set (lsuc (sℓ ⊔ℓ rℓ ⊔ℓ vℓ ⊔ℓ pℓ)) where
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
  : Set (lsuc (sℓ ⊔ℓ rℓ ⊔ℓ vℓ ⊔ℓ pℓ ⊔ℓ bℓ ⊔ℓ aℓ)) where
  field
    BuildView : Set bℓ
    Artifact : Set aℓ

    freeze :
      State K →
      ReceiptState G →
      ActiveView G →
      BuildView

    -- Nix belongs here: after the active selection has been frozen, never
    -- directly on an unresolved candidate state.
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
-- O, R, C, S, L, P, G, F.
--
-- L is the join-semilattice law carried by S.  C computes proposals; G
-- appends adjudication receipts and derives the effective view; F measures
-- unresolved multiplicity, policy debt, failed builds, or another chosen gap.

record InstitutionalModel
  {oℓ qℓ sℓ rℓ vℓ pℓ fℓ bℓ aℓ : Level}
  : Set (lsuc (oℓ ⊔ℓ qℓ ⊔ℓ sℓ ⊔ℓ rℓ ⊔ℓ vℓ ⊔ℓ pℓ ⊔ℓ fℓ ⊔ℓ bℓ ⊔ℓ aℓ)) where
  field
    O-Organization : Set oℓ
    R-Requirement : Set qℓ

    casey : CaseySubstrate {sℓ}
    governance :
      GovernanceLayer {rℓ = rℓ} {vℓ = vℓ} {pℓ = pℓ} casey
    buildBoundary :
      BuildBoundary {bℓ = bℓ} {aℓ = aℓ} casey governance

    C-Code :
      O-Organization →
      R-Requirement →
      State casey →
      Proposal governance

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
  : Set (oℓ ⊔ℓ qℓ ⊔ℓ sℓ ⊔ℓ rℓ ⊔ℓ vℓ ⊔ℓ pℓ ⊔ℓ fℓ) where
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
-- Fixed-point or Banach conclusions additionally require a concrete metric
-- or ultrametric, completeness, and a quantitative contraction law.  This
-- bridge records the strict gap-decrease boundary without inventing them.

record ContractionWitness
  {oℓ qℓ sℓ rℓ vℓ pℓ fℓ bℓ aℓ : Level}
  (M : InstitutionalModel
    {oℓ} {qℓ} {sℓ} {rℓ} {vℓ} {pℓ} {fℓ} {bℓ} {aℓ})
  : Set (lsuc (oℓ ⊔ℓ qℓ ⊔ℓ sℓ ⊔ℓ rℓ ⊔ℓ vℓ ⊔ℓ pℓ ⊔ℓ fℓ)) where
  field
    Unresolved :
      State (casey M) →
      ReceiptState (governance M) →
      Set fℓ

    StrictlyBelow : Gap M → Gap M → Set fℓ

    admissible-cycle-contracts :
      (cycle : GovernanceCycle M) →
      Unresolved (stateBefore cycle) (receiptsBefore cycle) →
      StrictlyBelow
        (F-Gap M (stateBefore cycle) (receiptsAfter cycle))
        (F-Gap M (stateBefore cycle) (receiptsBefore cycle))

open ContractionWitness public

------------------------------------------------------------------------
-- StatiBaker observer boundary.

record ObserverBoundary
  {sℓ rℓ vℓ pℓ refℓ : Level}
  (K : CaseySubstrate {sℓ})
  (G : GovernanceLayer {rℓ = rℓ} {vℓ = vℓ} {pℓ = pℓ} K)
  : Set (lsuc (sℓ ⊔ℓ rℓ ⊔ℓ vℓ ⊔ℓ pℓ ⊔ℓ refℓ)) where
  field
    ImmutableReference : Set refℓ

    stateReference : State K → ImmutableReference
    receiptReference : ReceiptState G → ImmutableReference
    activeViewReference : ActiveView G → ImmutableReference

open ObserverBoundary public
