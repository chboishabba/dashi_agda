module DASHI.Culture.ProvenancePreservingCulturalHyperfabric where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Provenance-preserving cultural hyperfabric.
--
-- National/religious/linguistic/community categories are cross-cutting
-- coordinates, not a forced two-value partition.  The module contains no
-- historical claim about any named population; concrete Palestine/Israel,
-- Jewish/Muslim/Christian, Ottoman, Sephardi, Mizrahi, Ashkenazi, Hasidic,
-- Arab, diaspora, etc. instances require their own evidence receipts.
------------------------------------------------------------------------

record CulturalHyperfabric : Set₁ where
  field
    Base : Set
    Point : Base → Set

    Memory : (b : Base) → Point b → Set
    Practice : (b : Base) → Point b → Set
    Relation : (b : Base) → Point b → Set
    Knowledge : (b : Base) → Point b → Set
    MaterialRelation : (b : Base) → Point b → Set
    Provenance : (b : Base) → Point b → Set

open CulturalHyperfabric public

record CrossCuttingCoordinate (H : CulturalHyperfabric) : Set₁ where
  field
    Coordinate : Set
    value : (b : Base H) → Point H b → Coordinate

open CrossCuttingCoordinate public

record PublicProjection (H : CulturalHyperfabric) : Set₁ where
  field
    Surface : Set
    project : (b : Base H) → Point H b → Surface

open PublicProjection public

------------------------------------------------------------------------
-- A public category can be useful without becoming the whole ontology.
------------------------------------------------------------------------

data ProjectionPromotesGlobalIdentity
    (H : CulturalHyperfabric)
    (P : PublicProjection H) : Set where

projectionDoesNotPromoteGlobalIdentity :
  ∀ {H P} → ProjectionPromotesGlobalIdentity H P → ⊥
projectionDoesNotPromoteGlobalIdentity ()

------------------------------------------------------------------------
-- Residual provenance remains independently representable.
------------------------------------------------------------------------

record ProjectionWithCulturalResidual
    (H : CulturalHyperfabric)
    (P : PublicProjection H) : Set₁ where
  field
    Residual : Set
    residual : (b : Base H) → Point H b → Residual
    ReopeningEvidence : Set
    reopeningEvidence :
      (b : Base H) →
      (x : Point H b) →
      ReopeningEvidence

open ProjectionWithCulturalResidual public

------------------------------------------------------------------------
-- Different memory fibres need not be equal for one hyperfabric to contain
-- them.  Shared formal machinery is not historical/moral equivalence.
------------------------------------------------------------------------

record DistinctMemoryFibres (H : CulturalHyperfabric) : Set₁ where
  field
    base : Base H
    left right : Point H base
    MemoryDistinction : Set
    memoryDistinction : MemoryDistinction

open DistinctMemoryFibres public

record CulturalHyperfabricBoundary : Set where
  constructor culturalHyperfabricBoundary
  field
    crossCuttingCoordinateIsExhaustiveIdentity : Bool
    crossCuttingCoordinateIsExhaustiveIdentityIsFalse :
      crossCuttingCoordinateIsExhaustiveIdentity ≡ false
    sameFormalMemoryCarrierMeansEquivalentHistory : Bool
    sameFormalMemoryCarrierMeansEquivalentHistoryIsFalse :
      sameFormalMemoryCarrierMeansEquivalentHistory ≡ false
    publicProjectionMayDestroyResidualByDefault : Bool
    publicProjectionMayDestroyResidualByDefaultIsFalse :
      publicProjectionMayDestroyResidualByDefault ≡ false

canonicalCulturalHyperfabricBoundary : CulturalHyperfabricBoundary
canonicalCulturalHyperfabricBoundary =
  culturalHyperfabricBoundary false refl false refl false refl
