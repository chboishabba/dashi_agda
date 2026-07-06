module DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNSchurResidueScale as ResidueScale
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)

------------------------------------------------------------------------
-- BKM / residence bridge surface.
--
-- The final NS-facing bridge must combine the Schur residue scale with a
-- separate residence-time or projection-smallness theorem. This module names
-- that dependency honestly.

record NSTriadKNBKMResidenceBridgeModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    schurResidueScaleModel :
      ResidueScale.NSTriadKNSchurResidueScaleModel {ℓS} {ℓE} {ℓV} {ℓR}

    ResidenceTimeExclusion : Set ℓR

    BKMProjectionSmallness : Set ℓR

    schurResidueScaleToBKMProjectionSmallness :
      ResidenceTimeExclusion ->
      BKMProjectionSmallness

    qGapAndResidenceExcludeBKMBlowup :
      ResidenceTimeExclusion ->
      BKMProjectionSmallness

open NSTriadKNBKMResidenceBridgeModel public

------------------------------------------------------------------------
-- Proof-derived gate definitions.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

bkmExclusionProved :
  QGap.ResidueScaleCompatibility → Bool
bkmExclusionProved compat with ResidueScale.schurResidueScaleClosed compat
... | true = true
... | false = false

bkmExclusionProvedIsTrue :
  (compat : QGap.ResidueScaleCompatibility) →
  QGap.compatibilityRouteClosed compat ≡ true →
  bkmExclusionProved compat ≡ true
bkmExclusionProvedIsTrue compat routeClosed
  rewrite ResidueScale.schurResidueScaleClosedIsTrue compat routeClosed = refl
