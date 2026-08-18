module DASHI.Cognition.PNF.ProducerNativeDemandProjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Producer-native provenance.
--
-- A demand producer may still have the exact bounded factor/support/slot fibre
-- from which occurrence provenance is defined. Materializing that fibre and
-- later searching the database to reconstruct the producer relation is only
-- admissible as an implementation when it is extensionally equal to the direct
-- producer projection. Once this equality is available, the reconstruction is
-- not semantic authority and may be bypassed by the producer-native path.
------------------------------------------------------------------------

record ProducerNativeProjection
  (Producer Materialized Provenance : Set)
  : Set₁ where
  field
    materialize : Producer → Materialized
    directProvenance : Producer → Provenance
    reconstructProvenance : Materialized → Provenance
    projectionExact : ∀ producer →
      directProvenance producer
      ≡ reconstructProvenance (materialize producer)

open ProducerNativeProjection public

producerNativeEqualsReconstruction :
  ∀ {Producer Materialized Provenance : Set}
    (law : ProducerNativeProjection Producer Materialized Provenance)
    (producer : Producer) →
  directProvenance law producer
  ≡ reconstructProvenance law (materialize law producer)
producerNativeEqualsReconstruction law producer = projectionExact law producer

------------------------------------------------------------------------
-- Demand-local statement factorization.
--
-- Constraint rows and initial horizon work are pure demand-local projections.
-- A statement-level PostgreSQL transition-table implementation is therefore
-- permitted only when projecting a list of demands is exactly the concatenation
-- of the pointwise projections. This is the algebra behind replacing N row
-- trigger invocations with one set operation over the inserted-demand fibre.
------------------------------------------------------------------------

_++ᵈ_ : ∀ {A : Set} → List A → List A → List A
[] ++ᵈ ys = ys
(x ∷ xs) ++ᵈ ys = x ∷ (xs ++ᵈ ys)

mapᵈ : ∀ {A B : Set} → (A → B) → List A → List B
mapᵈ f [] = []
mapᵈ f (x ∷ xs) = f x ∷ mapᵈ f xs

concatᵈ : ∀ {A : Set} → List (List A) → List A
concatᵈ [] = []
concatᵈ (xs ∷ xss) = xs ++ᵈ concatᵈ xss

record DemandLocalProjection (Demand Derived : Set) : Set₁ where
  field
    projectOne : Demand → List Derived
    projectStatement : List Demand → List Derived
    statementFactorizes : ∀ demands →
      projectStatement demands ≡ concatᵈ (mapᵈ projectOne demands)

open DemandLocalProjection public

statementProjectionEqualsPointwiseProjection :
  ∀ {Demand Derived : Set}
    (law : DemandLocalProjection Demand Derived)
    (demands : List Demand) →
  projectStatement law demands ≡ concatᵈ (mapᵈ (projectOne law) demands)
statementProjectionEqualsPointwiseProjection law demands =
  statementFactorizes law demands
