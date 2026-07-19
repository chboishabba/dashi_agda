module DASHI.Culture.Cuisine.CuisineFormalismBundle where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Culture.Cuisine.QualitativeSensoryCore as Q
import DASHI.Culture.Cuisine.DishIdentityLineageCore as D
import DASHI.Culture.Cuisine.CompositionProvenanceCore as C
import DASHI.Culture.Cuisine.CuisineDataFlowCore as F
import DASHI.Culture.Cuisine.CulinaryMovementCore as M

------------------------------------------------------------------------
-- Focused assembly of the culinary lane.  The bundle keeps material,
-- qualitative, historical, nutritional, provenance, and data-governance
-- carriers separate while permitting explicit bridges between them.
------------------------------------------------------------------------

record CuisineFormalismBundle (policy : F.PromotionPolicy) : Set₁ where
  field
    dishName            : String
    sensoryProfile      : Q.SensoryProfile
    observerContexts    : List Q.ObserverContext
    qualitativeReadings : List String
    lineageClaims       : List D.HistoricalClaim
    nutritionProfiles   : List C.NutritionVector
    provenanceChains    : List C.IngredientProvenance
    movementProjections : List M.DishMovementProjection
    sourceReceipts      : List F.SourceReceipt
    promotedClaims      : List (F.PromotedClaim policy)

open CuisineFormalismBundle public

data CuisineSurface : Set where
  sensorySurface safetySurface popularitySurface canonSurface
  nutritionSurface identitySurface provenanceSurface flavourSurface
  historicalSurface universalReadingSurface : CuisineSurface

data SurfaceDistinction : CuisineSurface → CuisineSurface → Set where
  sensorySafetyDistinct    : SurfaceDistinction sensorySurface safetySurface
  popularityCanonDistinct  : SurfaceDistinction popularitySurface canonSurface
  nutritionIdentityDistinct : SurfaceDistinction nutritionSurface identitySurface
  provenanceFlavourDistinct : SurfaceDistinction provenanceSurface flavourSurface
  historicalReceiptDistinct : SurfaceDistinction historicalSurface canonSurface
  observerUniversalDistinct : SurfaceDistinction sensorySurface universalReadingSurface

record CuisineNonCollapse : Set where
  field
    sensoryIsNotSafety            : SurfaceDistinction sensorySurface safetySurface
    popularityIsNotCanon          : SurfaceDistinction popularitySurface canonSurface
    nutritionIsNotIdentity        : SurfaceDistinction nutritionSurface identitySurface
    provenanceIsNotFlavour        : SurfaceDistinction provenanceSurface flavourSurface
    historicalClaimNeedsReceipt   : SurfaceDistinction historicalSurface canonSurface
    observerReadingIsNotUniversal : SurfaceDistinction sensorySurface universalReadingSurface

open CuisineNonCollapse public

canonicalCuisineNonCollapse : CuisineNonCollapse
canonicalCuisineNonCollapse = record
  { sensoryIsNotSafety = sensorySafetyDistinct
  ; popularityIsNotCanon = popularityCanonDistinct
  ; nutritionIsNotIdentity = nutritionIdentityDistinct
  ; provenanceIsNotFlavour = provenanceFlavourDistinct
  ; historicalClaimNeedsReceipt = historicalReceiptDistinct
  ; observerReadingIsNotUniversal = observerUniversalDistinct
  }
