module DASHI.Unified.FormalObjectParents where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Unified.InvariantSpine as Spine

------------------------------------------------------------------------
-- Parent table for the formal objects every DASHI facade object inherits.
--
-- This is the categorical reading requested by the facade: if a lane is
-- encoded as a DASHI unified object, it has these projections already present.
-- The status of each projection still records whether it is literal, soft, or
-- blocked for that lane.

canonicalProjectionKinds : List Spine.UniversalProjectionKind
canonicalProjectionKinds =
  Spine.modularJProjectionKind
  ∷ Spine.heckeProjectionKind
  ∷ Spine.bottProjectionKind
  ∷ Spine.kolmogorovProjectionKind
  ∷ Spine.categoryProjectionKind
  ∷ Spine.quotientProjectionKind
  ∷ Spine.latticeProjectionKind
  ∷ Spine.operatorProjectionKind
  ∷ []

record FormalObjectParentSurface : Set where
  field
    projectionKinds :
      List Spine.UniversalProjectionKind

    projectionKindsAreCanonical :
      projectionKinds ≡ canonicalProjectionKinds

    carrierOf :
      Spine.UniversalProjectionKind → Unified.LanguageCarrier

    carrierOfIsCanonical :
      carrierOf ≡ Spine.projectionCarrier

    inheritedProjection :
      Spine.UnifiedObjectInvariant →
      Spine.UniversalProjectionKind →
      Bool

    inheritedProjectionIsNonPromoting :
      ∀ object kind → inheritedProjection object kind ≡ false

    plainReading :
      String

canonicalFormalObjectParentSurface : FormalObjectParentSurface
canonicalFormalObjectParentSurface =
  record
    { projectionKinds =
        canonicalProjectionKinds
    ; projectionKindsAreCanonical =
        refl
    ; carrierOf =
        Spine.projectionCarrier
    ; carrierOfIsCanonical =
        refl
    ; inheritedProjection =
        Spine.objectProjectionPromotion
    ; inheritedProjectionIsNonPromoting =
        Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    ; plainReading =
        "Every DASHI unified facade object inherits the formal parent projections: modular-j, Hecke, Bott, Kolmogorov, category, quotient, lattice, and operator. Inheritance means the projection is categorically present as a typed carrier. Literal theorem authority is lane-specific; external promotion remains false by construction."
    }

kolmogorovCarrierIsCanonical :
  Spine.projectionCarrier Spine.kolmogorovProjectionKind
  ≡
  Unified.kolmogorovCarrier
kolmogorovCarrierIsCanonical =
  refl

heckeCarrierIsCanonical :
  Spine.projectionCarrier Spine.heckeProjectionKind
  ≡
  Unified.heckeCarrier
heckeCarrierIsCanonical =
  refl

bottCarrierIsCanonical :
  Spine.projectionCarrier Spine.bottProjectionKind
  ≡
  Unified.bottCarrier
bottCarrierIsCanonical =
  refl
