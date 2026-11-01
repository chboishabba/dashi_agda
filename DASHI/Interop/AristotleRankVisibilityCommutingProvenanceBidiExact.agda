module DASHI.Interop.AristotleRankVisibilityCommutingProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact as Commuting
import DASHI.Interop.AristotleRankQualifierPropertyEngineBoundary as Aristotle
import DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact as Item

-- Rank is statement-local; truthy visibility is computed from the whole covered
-- subject/property sibling family. Keep the coordinates distinct.
data StatementRank : Set where preferredRank normalRank deprecatedRank : StatementRank
data StatementVisibility : Set where truthyVisibility nonTruthyVisibility unresolvedVisibility : StatementVisibility

record RankVisibilityProjectionReceipt : Set where
  constructor rank-visibility-projection-receipt
  field
    subjectQidReference : String
    propertyReference : String
    statementReference : String
    siblingFamilyReference : String
    rankReference : String
    visibilityReference : String
    familyCoverageReference : String
    commutingSquareReference : String
open RankVisibilityProjectionReceipt public

-- A statement can retain normal rank while its visibility changes when a
-- preferred sibling is added. Same local rank is not same projection history.
data SameRankImpliesSameVisibility : Set where
sameRankDoesNotDetermineVisibility : SameRankImpliesSameVisibility → ⊥
sameRankDoesNotDetermineVisibility ()

-- Matching visible outputs along one observation path do not replace the
-- provenance square that records dependence on the whole sibling family.
data SameObservedVisibilityImpliesCommutingProjection : Set where
observedAgreementDoesNotCreateCommutingSquare :
  SameObservedVisibilityImpliesCommutingProjection → ⊥
observedAgreementDoesNotCreateCommutingSquare ()

record AristotleRankVisibilityCommutingBoundary : Set where
  constructor aristotle-rank-visibility-commuting-boundary
  field
    rankAndVisibilityDistinct : Bool
    visibilityDependsOnSiblingFamily : Bool
    sameRankForcesSameVisibility : Bool
    trajectoryAgreementReplacesCommutingReceipt : Bool

canonicalAristotleRankVisibilityCommutingBoundary :
  AristotleRankVisibilityCommutingBoundary
canonicalAristotleRankVisibilityCommutingBoundary =
  aristotle-rank-visibility-commuting-boundary true true false false

rankVisibilityCommutingStatement : String
rankVisibilityCommutingStatement =
  "A Wikidata statement's preferred/normal/deprecated rank is local metadata, while truthy/non-truthy visibility is a projection of the covered Q/P sibling family. Equal local rank or equal observed visibility does not establish the same provenance transformation; the projection must retain its whole-family commuting receipt."
