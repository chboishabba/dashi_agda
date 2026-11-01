module DASHI.Compression.DashiGuidedSearch where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Compression.StringMDLCore

------------------------------------------------------------------------
-- DASHI embedding as search guidance only.
--
-- Coordinates may be integer-, floating-, residue-, tree-, ultrametric-, or
-- graph-derived.  No coordinate or proposal score can authorize a move.
------------------------------------------------------------------------

record DashiStringEmbedding (M : StringMDLSystem) : Set₁ where
  field
    Coordinate : Set

    embed : String → Coordinate

    -- Cheap integer-friendly proposal observables.
    coarseAddress : Coordinate → Nat
    distance      : Coordinate → Coordinate → Nat
    operationCost : Move M → Nat

    -- Approximate and incomplete proposal order is permitted.
    propose : State M → List (Move M)
    prior   : State M → Move M → Nat

open DashiStringEmbedding public

------------------------------------------------------------------------
-- Constructive membership for heuristic proposal lists.
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Exact gate.  The guide supplies a candidate; the MDL witness authorizes it.
------------------------------------------------------------------------

record GuidedExactStep
  (M : StringMDLSystem)
  (E : DashiStringEmbedding M)
  (s : State M)
  : Set where
  field
    candidate : Move M
    proposed  : candidate ∈ propose E s

    -- Acceptance remains entirely in the exact MDL layer.
    exact    : ExactImprovement M s
    sameMove : candidate ≡ move exact

open GuidedExactStep public

guided-step-strictly-descends :
  (M : StringMDLSystem) →
  (E : DashiStringEmbedding M) →
  (s : State M) →
  (g : GuidedExactStep M E s) →
  totalLength M (apply M s (candidate g)) < totalLength M s
guided-step-strictly-descends M E s g rewrite sameMove g = strictMDL (exact g)

guided-step-preserves-source :
  (M : StringMDLSystem) →
  (E : DashiStringEmbedding M) →
  (s : State M) →
  (g : GuidedExactStep M E s) →
  sourceText M (apply M s (candidate g)) ≡ sourceText M s
guided-step-preserves-source M E s g rewrite sameMove g =
  accepted-preserves-source M s (exact g)

------------------------------------------------------------------------
-- Proposal-order invariance.
--
-- Two guides may order or cluster candidates differently.  If they present
-- the same exact improvement witness, the resulting state is definitionally
-- the same because apply belongs to the MDL system, not to either guide.
------------------------------------------------------------------------

proposal-order-cannot-change-application :
  (M : StringMDLSystem) →
  (E₁ E₂ : DashiStringEmbedding M) →
  (s : State M) →
  (m : Move M) →
  apply M s m ≡ apply M s m
proposal-order-cannot-change-application M E₁ E₂ s m = refl

record HeuristicAuthorityBoundary : Set where
  field
    embeddingGuidesSearch        : Bool
    embeddingGuidesSearchIsTrue  : embeddingGuidesSearch ≡ true
    embeddingAcceptsMoves        : Bool
    embeddingAcceptsMovesIsFalse : embeddingAcceptsMoves ≡ false
    mdlOracleRemainsExact        : Bool
    mdlOracleRemainsExactIsTrue  : mdlOracleRemainsExact ≡ true

canonicalHeuristicAuthorityBoundary : HeuristicAuthorityBoundary
canonicalHeuristicAuthorityBoundary =
  record
    { embeddingGuidesSearch = true
    ; embeddingGuidesSearchIsTrue = refl
    ; embeddingAcceptsMoves = false
    ; embeddingAcceptsMovesIsFalse = refl
    ; mdlOracleRemainsExact = true
    ; mdlOracleRemainsExactIsTrue = refl
    }
