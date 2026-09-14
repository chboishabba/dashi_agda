module DASHI.Papers.NavierStokes.PublishedProofBidiProvenanceValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.PublishedProofBidiProvenanceExact as Bidi

publishedForcedBlowupRecorded :
  Bidi.publishedForcedBlowupRecorded ≡ true
publishedForcedBlowupRecorded = refl

publishedForcedBlowupIsNotUnforcedRegularity :
  Bidi.publishedForcedBlowupSameStatementAsDashiUnforcedRegularity ≡ false
publishedForcedBlowupIsNotUnforcedRegularity = refl

citationDoesNotImportPublishedProof :
  Bidi.externalCitationImportsProof ≡ false
citationDoesNotImportPublishedProof = refl

historicalPaperOneRouteRetained :
  Bidi.historicalA1A9RouteRetained ≡ true
historicalPaperOneRouteRetained = refl

pr890GeometryOnlySeparationRejected :
  Bidi.pr890GeometryOnlySeparationSufficient ≡ false
pr890GeometryOnlySeparationRejected = refl

bidiConstructionComparisonOpen :
  Bidi.dashiConstructsPublishedForcedBlowupProof ≡ false
bidiConstructionComparisonOpen = refl

unforcedClayPromotionStillFalse :
  Bidi.dashiUnforcedPeriodicClayPromotion ≡ false
unforcedClayPromotionStillFalse = refl
