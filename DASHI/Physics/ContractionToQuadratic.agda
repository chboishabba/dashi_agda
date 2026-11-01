{-# OPTIONS --safe #-}

module DASHI.Physics.ContractionToQuadratic where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Data.Unit.Polymorphic as PU using (⊤; tt)

open import DASHI.Physics.Core

-- Canonical realized witnesses for the current repo snapshot live in
-- `DASHI.Physics.Closure.*`. This module stays --safe and only defines
-- stable interface records; consumers wanting realized content should
-- import the closure modules directly (or go through Closure summaries).

-- A “kernel symmetry” / invariance predicate.
record Invariant {ℓ : Level} {V : Set ℓ} (T : V → V) (Q : Quadratic V) : Set (suc ℓ) where
  field
    inv : ∀ v → Quadratic.Q Q (T v) ≡ Quadratic.Q Q v

-- Existence witness for a quadratic form.
record QuadraticWitness {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    Q : Quadratic V

-- Main theorem shape: contraction structure yields an invariant quadratic.
record ContractionForcesQuadratic {ℓ : Level} (M : MetricSpace ℓ) : Set (suc (suc ℓ)) where
  open MetricSpace M
  field
    toV      : X → X            -- placeholder if your V is X itself
    theorem  :
      (C : ContractionOp M) →
      Σ (QuadraticWitness X) (λ W → Invariant (ContractionOp.T C) (QuadraticWitness.Q W))

-- Stronger “admissible quadratic” interface that bundles all invariances.
record AdmissibleQuadratic
       {ℓ : Level}
       (V   : Set ℓ)
       (T   : V → V)
       (iso : Isotropy V)
       (ι   : Involution V)
       (fs  : FiniteSpeed V)
       : Set (suc (suc ℓ)) where
  field
    Q                  : Quadratic V
    invariantUnderT    : Invariant T Q
    invariantUnderIso  : PreservesQuadratic iso Q
    involutionCompat   : ∀ v → Quadratic.Q Q (Involution.ι ι v) ≡ Quadratic.Q Q v
    finiteSpeedCompat  : FiniteSpeed.locality fs

-- Uniqueness up to scale / gauge.
record UniqueUpToScale {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    uniq : Set ℓ

record ContractionForcesQuadraticAxioms {ℓ : Level} (M : MetricSpace ℓ) : Set (suc (suc ℓ)) where
  field
    witness : ContractionForcesQuadratic M

contraction⇒invariantQuadratic :
  ∀ {ℓ} {M : MetricSpace ℓ} →
  ContractionForcesQuadraticAxioms M →
  ContractionForcesQuadratic M
contraction⇒invariantQuadratic ax =
  ContractionForcesQuadraticAxioms.witness ax

record AdmissibleQuadraticUniquenessAxioms
       {ℓ : Level}
       {V : Set ℓ}
       {T   : V → V}
       {iso : Isotropy V}
       {ι   : Involution V}
       {fs  : FiniteSpeed V} : Set (suc (suc ℓ)) where
  field
    uniq :
      (Q₁ Q₂ : AdmissibleQuadratic V T iso ι fs) →
      UniqueUpToScale V

admissibleQuadraticUnique :
  ∀ {ℓ} {V : Set ℓ}
    {T   : V → V}
    {iso : Isotropy V}
    {ι   : Involution V}
    {fs  : FiniteSpeed V} →
    AdmissibleQuadraticUniquenessAxioms {V = V} {T = T} {iso = iso} {ι = ι} {fs = fs} →
    (Q₁ Q₂ : AdmissibleQuadratic V T iso ι fs) →
    UniqueUpToScale V
admissibleQuadraticUnique ax = AdmissibleQuadraticUniquenessAxioms.uniq ax

record ContractionUniqueQuadraticAxioms {ℓ : Level} (M : MetricSpace ℓ) : Set (suc (suc ℓ)) where
  field
    unique :
      (C : ContractionOp M) →
      UniqueUpToScale (MetricSpace.X M)

contraction⇒uniqueQuadraticUpToScale :
  ∀ {ℓ} {M : MetricSpace ℓ} →
  ContractionUniqueQuadraticAxioms M →
  (C : ContractionOp M) →
  UniqueUpToScale (MetricSpace.X M)
contraction⇒uniqueQuadraticUpToScale ax =
  ContractionUniqueQuadraticAxioms.unique ax
