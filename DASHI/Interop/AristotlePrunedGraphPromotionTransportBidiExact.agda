module DASHI.Interop.AristotlePrunedGraphPromotionTransportBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.PromotionTransportChainBidiExact as Promotion
import DASHI.Interop.ZelphPrunedArtifactQueryPreservationExact as Preservation
import DASHI.Interop.AristotleConservativeTypeModuleBoundaryExact as TypeModule

record PrunedGraphTransportStage : Set where
  constructor pruned-graph-transport-stage
  field
    artifactReference : String
    routedObservationReference : String
    queryFamilyReference : String
    soundnessReference : String
    typeModuleReference : String
    nativeGraphAlignmentReference : String
    consumerEvidenceReference : String
    positiveSoundnessPaid : Bool
    negativeCompletenessPaid : Bool
open PrunedGraphTransportStage public

-- Concrete reciprocal transport firewall: a sound retained answer can move
-- forward as evidence, but it does not backfill completeness or promotion.
data PositiveSoundnessImpliesNegativeCompleteness : Set where
positiveSoundnessDoesNotCreateNegativeCompleteness :
  PositiveSoundnessImpliesNegativeCompleteness → ⊥
positiveSoundnessDoesNotCreateNegativeCompleteness ()

data PrePromotionTransportImpliesMigrationAuthority : Set where
prePromotionDoesNotCreateMigrationAuthority :
  PrePromotionTransportImpliesMigrationAuthority → ⊥
prePromotionDoesNotCreateMigrationAuthority ()

record AristotlePrunedPromotionBoundary : Set where
  constructor aristotle-pruned-promotion-boundary
  field
    artifactExistenceDistinctFromRoutedObservation : Bool
    routedObservationDistinctFromSoundness : Bool
    soundnessDistinctFromCompleteness : Bool
    typeModuleDistinctFromNativeStatementAlignment : Bool
    consumerEvidenceDistinctFromPromotion : Bool

canonicalAristotlePrunedPromotionBoundary : AristotlePrunedPromotionBoundary
canonicalAristotlePrunedPromotionBoundary =
  aristotle-pruned-promotion-boundary true true true true true

prunedPromotionStatement : String
prunedPromotionStatement =
  "For a pruned Zelph/Wikidata artifact, artifact existence, routed relation observation, query-family soundness, negative completeness, type-module construction, native/graph alignment, consumer evidence and promotion remain distinct transport obligations. Positive soundness can support retained answers but cannot create negative completeness or migration authority."
