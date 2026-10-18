{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRAnchoredSharedEffectiveSourceExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared

------------------------------------------------------------------------
-- CANONICAL GR-ANCHORED SHARED SOURCE
--
-- Define the shared source to be the literal GR source itself, represented in
-- UnifiedCandidate.SharedStressEnergy.  This does not prove any QFT equality;
-- it merely makes the GR factorisation definitional so the cross-sector burden
-- sits exactly where it belongs.
------------------------------------------------------------------------

grAnchoredSharedSource :
  (U : Weld.UnifiedCandidate) →
  Shared.SharedEffectiveSourceTheory U
grAnchoredSharedSource U = record
  { Shared.SharedEffectiveSourceTheory.effectiveSource =
      λ candidate _ →
        Weld.grStressToShared U candidate
          (Weld.actualGRStressEnergy U candidate)
  ; Shared.SharedEffectiveSourceTheory.sourceAfterCoarseGraining =
      λ candidate regime →
        Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
          (Weld.actualGRStressEnergy U
            (Weld.coarseGrain U candidate regime))
  ; Shared.SharedEffectiveSourceTheory.sourceCoarseGrainingCommutes =
      λ _ _ → refl
  }

grAnchoredSourceFactorisesGR :
  ∀ {U : Weld.UnifiedCandidate} →
  Shared.GRSourceFactorisation (grAnchoredSharedSource U)
grAnchoredSourceFactorisesGR = record
  { Shared.GRSourceFactorisation.grSourceFactorises =
      λ _ _ _ → refl
  }

grFactorisationIsPrimitiveOnGRAnchoredRoute : Bool
grFactorisationIsPrimitiveOnGRAnchoredRoute = false

grFactorisationIsPrimitiveOnGRAnchoredRouteIsFalse :
  grFactorisationIsPrimitiveOnGRAnchoredRoute ≡ false
grFactorisationIsPrimitiveOnGRAnchoredRouteIsFalse = refl

crossSectorStressEqualityStillPhysical : Bool
crossSectorStressEqualityStillPhysical = true

crossSectorStressEqualityStillPhysicalIsTrue :
  crossSectorStressEqualityStillPhysical ≡ true
crossSectorStressEqualityStillPhysicalIsTrue = refl
