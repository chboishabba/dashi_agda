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

------------------------------------------------------------------------
-- Superseded projection elision with live-residue extraction.
------------------------------------------------------------------------

record SupersededProjectionElision
  (Source Legacy Replacement Consumer Observation : Set)
  : Set₁ where
  field
    legacyProjection : Source → Legacy
    replacementProjection : Source → Replacement
    observeLegacy : Consumer → Legacy → Observation
    observeReplacement : Consumer → Replacement → Observation
    allLiveConsumersPreserved : ∀ consumer source →
      observeLegacy consumer (legacyProjection source)
      ≡ observeReplacement consumer (replacementProjection source)

open SupersededProjectionElision public

replacementPreservesEveryLiveConsumer :
  ∀ {Source Legacy Replacement Consumer Observation : Set}
    (law : SupersededProjectionElision
      Source Legacy Replacement Consumer Observation)
    (consumer : Consumer)
    (source : Source) →
  observeLegacy law consumer (legacyProjection law source)
  ≡ observeReplacement law consumer (replacementProjection law source)
replacementPreservesEveryLiveConsumer law consumer source =
  allLiveConsumersPreserved law consumer source

------------------------------------------------------------------------
-- Sparse live residue.
------------------------------------------------------------------------

record LiveObligationExtraction
  (Source Legacy Replacement Obligation : Set)
  : Set₁ where
  field
    legacyObligations : Legacy → List Obligation
    replacementObligations : Replacement → List Obligation
    legacyFromSource : Source → Legacy
    replacementFromSource : Source → Replacement
    liveObligationsExact : ∀ source →
      legacyObligations (legacyFromSource source)
      ≡ replacementObligations (replacementFromSource source)

open LiveObligationExtraction public

replacementRetainsAllLiveObligations :
  ∀ {Source Legacy Replacement Obligation : Set}
    (law : LiveObligationExtraction Source Legacy Replacement Obligation)
    (source : Source) →
  legacyObligations law (legacyFromSource law source)
  ≡ replacementObligations law (replacementFromSource law source)
replacementRetainsAllLiveObligations law source =
  liveObligationsExact law source

------------------------------------------------------------------------
-- Cold exact rebuild.
--
-- Once every live production consumer has factored through Replacement, a
-- superseded Legacy carrier need not remain transactionally hot merely because
-- audit/compatibility tooling may still inspect it.  The cold carrier remains
-- legitimate only when an explicit rebuild from current source authority is
-- extensionally equal to the historical Legacy projection.
--
-- This is the formal boundary used when migration-122 occurrence support is
-- removed from automatic demand/export maintenance while preserving a set-wise
-- explicit audit rebuild.  Cold does not mean approximate or stale-by-design:
-- it means "rebuild before a consumer which explicitly requests Legacy".
------------------------------------------------------------------------

record ColdRebuildableProjection
  (Source Legacy : Set)
  : Set₁ where
  field
    legacyFromCurrentSource : Source → Legacy
    rebuildCold : Source → Legacy
    coldRebuildExact : ∀ source →
      rebuildCold source ≡ legacyFromCurrentSource source

open ColdRebuildableProjection public

coldRebuildPreservesLegacyObservation :
  ∀ {Source Legacy : Set}
    (law : ColdRebuildableProjection Source Legacy)
    (source : Source) →
  rebuildCold law source ≡ legacyFromCurrentSource law source
coldRebuildPreservesLegacyObservation law source = coldRebuildExact law source
