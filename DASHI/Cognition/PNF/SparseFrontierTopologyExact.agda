module DASHI.Cognition.PNF.SparseFrontierTopologyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Canonical containment and overlapping evidence fibres are different edge
-- species. Canonical LEAVES and canonical PARENT frontiers are different
-- reduction roles as well: sharing a containment topology does not authorize a
-- leaf interface to run the parent-frontier reducer.
------------------------------------------------------------------------

data ⊥ᶠ : Set where

record FrontierTopology (Interface : Set) : Set₁ where
  field
    Canonical : Interface → Set
    ParentFrontier : Interface → Set
    Leaf : Interface → Set
    Overlapping : Interface → Set
    parent : Interface → Interface → Set
    supports : Interface → Interface → Set

    canonicalOverlapDisjoint :
      ∀ interface → Canonical interface → Overlapping interface → ⊥ᶠ

    parentFrontierRequiresCanonical :
      ∀ interface → ParentFrontier interface → Canonical interface

    leafRequiresCanonical :
      ∀ interface → Leaf interface → Canonical interface

    parentLeafDisjoint :
      ∀ interface → ParentFrontier interface → Leaf interface → ⊥ᶠ

    parentRequiresCanonical :
      ∀ child parentInterface → parent child parentInterface → Canonical child

open FrontierTopology public

record CanonicalReductionBoundary
  (Interface : Set)
  (topology : FrontierTopology Interface)
  : Set₁ where
  field
    reducible : Interface → Set
    reducibleIffParentFrontier :
      ∀ interface → reducible interface ≡ ParentFrontier topology interface

open CanonicalReductionBoundary public

substᶠ : ∀ {A B : Set} → A ≡ B → A → B
substᶠ refl value = value

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
    (parentFrontierRequiresCanonical topology interface parentProof)
    overlap
  where
  parentProof : ParentFrontier topology interface
  parentProof = substᶠ (reducibleIffParentFrontier boundary interface) canReduce

canonicalParentReducerRejectsLeaf :
  ∀ {Interface : Set}
    {topology : FrontierTopology Interface}
    (boundary : CanonicalReductionBoundary Interface topology)
    (interface : Interface) →
    Leaf topology interface →
    reducible boundary interface →
    ⊥ᶠ
canonicalParentReducerRejectsLeaf {topology = topology} boundary interface leaf canReduce =
  parentLeafDisjoint topology interface parentProof leaf
  where
  parentProof : ParentFrontier topology interface
  parentProof = substᶠ (reducibleIffParentFrontier boundary interface) canReduce

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
