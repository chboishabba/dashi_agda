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
-- Producer-known coordinates.
--
-- The parser producer already knows coordinates such as sentence identity and
-- the declared same-sentence dependency-head span. A compatibility writer may
-- materialize a textual/key coordinate and recover the numeric coordinate by a
-- later lookup, but that lookup is not semantic authority once the producer's
-- supplied coordinate is proved equal to recovery from the same materialized
-- state. This is the formal boundary used by the strict numeric COPY path.
------------------------------------------------------------------------

record ProducerKnownCoordinate
  (Producer Materialized Key Coordinate : Set)
  : Set₁ where
  field
    materializeCoordinate : Producer → Materialized
    lookupKey : Producer → Key
    suppliedCoordinate : Producer → Coordinate
    recoverCoordinate : Materialized → Key → Coordinate
    suppliedEqualsRecovered : ∀ producer →
      suppliedCoordinate producer
      ≡ recoverCoordinate
          (materializeCoordinate producer)
          (lookupKey producer)

open ProducerKnownCoordinate public

knownCoordinateEliminatesRecoveryAsAuthority :
  ∀ {Producer Materialized Key Coordinate : Set}
    (law : ProducerKnownCoordinate Producer Materialized Key Coordinate)
    (producer : Producer) →
  suppliedCoordinate law producer
  ≡ recoverCoordinate law
      (materializeCoordinate law producer)
      (lookupKey law producer)
knownCoordinateEliminatesRecoveryAsAuthority law producer =
  suppliedEqualsRecovered law producer

------------------------------------------------------------------------
-- Demand-local statement factorization.
--
-- Constraint rows, initial horizon work, parser sentence-region/work rows and
-- other pure derived relations are pointwise projections of a finite inserted
-- carrier. A statement-level transition-table implementation is permitted only
-- when projecting the whole list is exactly the concatenation of the pointwise
-- projections. This is the algebra behind replacing N row-trigger invocations
-- with one set operation over the inserted fibre.
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

------------------------------------------------------------------------
-- Pre-aggregated finite lookup.
--
-- A set-wise implementation may compute a finite support summary once and join
-- every occurrence against it. The optimization is admissible only when the
-- aggregate lookup agrees with the original pointwise lookup for every key.
-- This is the exact law used to replace repeated correlated uniqueness probes
-- by one grouped token/object support relation.
------------------------------------------------------------------------

record PreaggregatedLookup
  (Source Key Value Summary : Set)
  : Set₁ where
  field
    summarize : Source → Summary
    pointLookup : Source → Key → Value
    summaryLookup : Summary → Key → Value
    aggregateExact : ∀ source key →
      pointLookup source key ≡ summaryLookup (summarize source) key

open PreaggregatedLookup public

preaggregationPreservesLookup :
  ∀ {Source Key Value Summary : Set}
    (law : PreaggregatedLookup Source Key Value Summary)
    (source : Source)
    (key : Key) →
  pointLookup law source key ≡ summaryLookup law (summarize law source) key
preaggregationPreservesLookup law source key = aggregateExact law source key
