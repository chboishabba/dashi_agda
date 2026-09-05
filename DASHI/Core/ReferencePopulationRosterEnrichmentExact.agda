module DASHI.Core.ReferencePopulationRosterEnrichmentExact where

------------------------------------------------------------------------
-- REFERENCE-POPULATION ROSTER ENRICHMENT
--
-- A feature cannot be called unusually concentrated in a roster merely because
-- it occurs several times.  A comparison population and denominator are part of
-- the theorem object.  Rates are compared without division by cross-multiplying
-- natural-number counts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record PopulationFeatureCount : Set where
  constructor population-feature-count
  field
    populationLabel : String
    populationSize : Nat
    featureCount : Nat
    constructionReference : String
    featureScoringReference : String

open PopulationFeatureCount public

record MatchedReferenceDesign : Set where
  constructor matched-reference-design
  field
    rosterDefinition : String
    referencePopulationDefinition : String
    matchingAxes : List String
    featureDefinitionFixedBeforeControlScoring : Bool
    featureDefinitionFixedBeforeControlScoringIsTrue :
      featureDefinitionFixedBeforeControlScoring ≡ true
    inclusionRuleReference : String
    exclusionRuleReference : String

open MatchedReferenceDesign public

------------------------------------------------------------------------
-- rosterCount / rosterSize > controlCount / controlSize
-- iff rosterCount * controlSize > controlCount * rosterSize,
-- assuming meaningful nonzero denominators supplied by the application.
------------------------------------------------------------------------

record PositivePopulationSize (count : PopulationFeatureCount) : Set where
  constructor positive-population-size
  field
    witness : 0 < populationSize count

open PositivePopulationSize public

record FeatureEnriched
    (roster control : PopulationFeatureCount) : Set where
  constructor feature-enriched
  field
    rosterNonzero : PositivePopulationSize roster
    controlNonzero : PositivePopulationSize control
    crossProductGreater :
      featureCount control * populationSize roster <
      featureCount roster * populationSize control
    comparisonReference : String

open FeatureEnriched public

record FeatureNotEnriched
    (roster control : PopulationFeatureCount) : Set where
  constructor feature-not-enriched
  field
    noGreaterRate :
      featureCount roster * populationSize control ≤
      featureCount control * populationSize roster
    comparisonReference : String

open FeatureNotEnriched public

record EnrichmentBoundary : Set where
  constructor enrichment-boundary
  field
    multipleRosterMatchesAloneEstablishEnrichment : Bool
    multipleRosterMatchesAloneEstablishEnrichmentIsFalse :
      multipleRosterMatchesAloneEstablishEnrichment ≡ false

    denominatorRequiredForEnrichmentClaim : Bool
    denominatorRequiredForEnrichmentClaimIsTrue :
      denominatorRequiredForEnrichmentClaim ≡ true

    matchedControlsMayBeChosenAfterFeatureScoresAreKnown : Bool
    matchedControlsMayBeChosenAfterFeatureScoresAreKnownIsFalse :
      matchedControlsMayBeChosenAfterFeatureScoresAreKnown ≡ false

    enrichmentAutomaticallyImpliesCausalSelection : Bool
    enrichmentAutomaticallyImpliesCausalSelectionIsFalse :
      enrichmentAutomaticallyImpliesCausalSelection ≡ false

    failureToFindEnrichmentMayWeakenCandidateFeature : Bool
    failureToFindEnrichmentMayWeakenCandidateFeatureIsTrue :
      failureToFindEnrichmentMayWeakenCandidateFeature ≡ true

canonicalEnrichmentBoundary : EnrichmentBoundary
canonicalEnrichmentBoundary = enrichment-boundary
  false refl
  true refl
  false refl
  false refl
  true refl
