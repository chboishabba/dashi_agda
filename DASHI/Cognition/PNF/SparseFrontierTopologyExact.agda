module DASHI.Cognition.PNF.SparseFrontierTopologyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Canonical containment and overlapping evidence fibres are different edge
-- species. A shared Interface carrier does not authorize one reduction law.
------------------------------------------------------------------------

data ⊥ᶠ : Set where

record FrontierTopology (Interface : Set) : Set₁ where
  field
    Canonical : Interface → Set
    Overlapping : Interface → Set
    parent : Interface → Interface → Set
    supports : Interface → Interface → Set

    canonicalOverlapDisjoint :
      ∀ interface → Canonical interface → Overlapping interface → ⊥ᶠ

    parentRequiresCanonical :
      ∀ child parentInterface → parent child parentInterface → Canonical child

open FrontierTopology public

record CanonicalReductionBoundary
  (Interface : Set)
  (topology : FrontierTopology Interface)
  : Set₁ where
  field
    reducible : Interface → Set
    reducibleIffCanonical :
      ∀ interface → reducible interface ≡ Canonical topology interface

open CanonicalReductionBoundary public

canonicalReducerRejectsOverlap :
  ∀ {Interface : Set}
    {topology : FrontierTopology Interface}
    (boundary : CanonicalReductionBoundary Interface topology)
    (interface : Interface) →
    Overlapping topology interface →
    reducible boundary interface →
    ⊥ᶠ
canonicalReducerRejectsOverlap {topology = topology} boundary interface overlap canReduce =
  canonicalOverlapDisjoint topology interface
    (substᶠ (reducibleIffCanonical boundary interface) canReduce)
    overlap
  where
  substᶠ : ∀ {A B : Set} → A ≡ B → A → B
  substᶠ refl value = value

------------------------------------------------------------------------
-- Sparse dirty closure.
--
-- Canonical child change may dirty exactly its canonical parent. This is the
-- local transition rule that replaces a complete document-wide safety sweep.
------------------------------------------------------------------------

record ExactParentDirtying
  (Interface : Set)
  (topology : FrontierTopology Interface)
  : Set₁ where
  field
    changed : Interface → Set
    dirty : Interface → Set
    dirtyExact :
      ∀ parentInterface →
      dirty parentInterface
      ≡
      Σ Interface (λ child →
        Σ (changed child) (λ _ → parent topology child parentInterface))

open ExactParentDirtying public

parentDirtyingHasNoUnrelatedInterfaces :
  ∀ {Interface : Set}
    {topology : FrontierTopology Interface}
    (proof : ExactParentDirtying Interface topology)
    (parentInterface : Interface) →
  dirty proof parentInterface
  ≡
  Σ Interface (λ child →
    Σ (changed proof child) (λ _ → parent topology child parentInterface))
parentDirtyingHasNoUnrelatedInterfaces proof parentInterface =
  dirtyExact proof parentInterface

------------------------------------------------------------------------
-- Residual-only adjacency and root publication.
--
-- If overlapping evidence is deliberately not consumed by the current root
-- consumer, closing that evidence fibre cannot change the root observation.
-- A second root publication is therefore observationally idempotent. This
-- theorem does NOT say the evidence is irrelevant to every future consumer.
------------------------------------------------------------------------

record ResidualOnlyAdjacencyObservation (Root Evidence Observation : Set) : Set₁ where
  field
    observeRoot : Root → Observation
    beforeRoot : Root
    afterRoot : Root
    evidence : Evidence
    evidenceNotConsumedByRoot : observeRoot beforeRoot ≡ observeRoot afterRoot

open ResidualOnlyAdjacencyObservation public

secondRootPublicationIsObservationallyIdempotent :
  ∀ {Root Evidence Observation : Set}
    (proof : ResidualOnlyAdjacencyObservation Root Evidence Observation) →
  observeRoot proof (beforeRoot proof) ≡ observeRoot proof (afterRoot proof)
secondRootPublicationIsObservationallyIdempotent proof =
  evidenceNotConsumedByRoot proof
