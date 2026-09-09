module DASHI.Interop.AristotlePropertyFamilyQueryFibreBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact as Query
import DASHI.Interop.SensibLawWikidataRequiredPropertyCoverageExact as Coverage
import DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact as Item

-- Concrete reciprocal instantiation: a Wikidata consumer is indexed by the
-- subject/property family Q/P, not by the whole item or whole graph.
record PropertyFamilyQueryFibreReceipt : Set where
  constructor property-family-query-fibre-receipt
  field
    subjectQidReference : String
    propertyReference : String
    coverageReference : String
    statementFamilyReference : String
    consumerReference : String
    familyCoverageObserved : Bool
    familyCoverageObservedIsTrue : familyCoverageObserved ≡ true
    wholeItemComplete : Bool
open PropertyFamilyQueryFibreReceipt public

-- A local Q/P consumer may close without identifying the entire item.
data ConsumerClosureImpliesWholeItemCompleteness : Set where
consumerClosureDoesNotRequireWholeItemCompleteness :
  ConsumerClosureImpliesWholeItemCompleteness → ⊥
consumerClosureDoesNotRequireWholeItemCompleteness ()

-- Conversely, an uninspected/incomplete Q/P family cannot pay rank visibility
-- merely because some sibling statement happened to be returned.
data PartialFamilyObservationDeterminesTruthyVisibility : Set where
partialFamilyDoesNotDetermineTruthyVisibility :
  PartialFamilyObservationDeterminesTruthyVisibility → ⊥
partialFamilyDoesNotDetermineTruthyVisibility ()

record AristotlePropertyFamilyQueryFibreBoundary : Set where
  constructor aristotle-property-family-query-fibre-boundary
  field
    queryAndPropertyFamilyJointlyIndexEvidence : Bool
    qPCoverageMayCloseLocalConsumer : Bool
    localConsumerClosureRequiresWholeItemCompleteness : Bool
    partialQPCoverageDeterminesTruthyVisibility : Bool

canonicalAristotlePropertyFamilyQueryFibreBoundary :
  AristotlePropertyFamilyQueryFibreBoundary
canonicalAristotlePropertyFamilyQueryFibreBoundary =
  aristotle-property-family-query-fibre-boundary true true false false

propertyFamilyQueryFibreStatement : String
propertyFamilyQueryFibreStatement =
  "Aristotle/Wikidata rank and visibility consumers live on a subject-property family Q/P. Complete coverage of that family may close that local consumer while the whole item remains non-singleton or incomplete; incomplete or uninspected family coverage cannot determine truthy visibility because an unseen preferred sibling could change the projection."
