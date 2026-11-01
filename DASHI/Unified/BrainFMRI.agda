module DASHI.Unified.BrainFMRI where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Physics.Closure.BidirectionalBrainObservationQuotient as Bidirectional
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as FMRI
import DASHI.Unified.InvariantSpine as Spine

brainFirstMissing : FMRI.BrainObservationFirstMissing
brainFirstMissing =
  FMRI.missingEmpiricalComparisonRun

bidirectionalFirstMissing : Bidirectional.BidirectionalObservationFirstMissing
bidirectionalFirstMissing =
  Bidirectional.missingLatentStateModelReceipt

brainNonPromotionBoundary : Bidirectional.NonPromotionBoundary
brainNonPromotionBoundary =
  Bidirectional.noLatentStateRecovery

brainFMRIObject : Spine.UnifiedObjectInvariant
brainFMRIObject =
  Spine.unifiedObjectInvariant
    "brain-fmri-observation-parent"
    Unified.brainLane
    "connectome-constrained fMRI, behavior, and body-resource quotient observations"
    "latent/phase observation -> lossy quotient surface -> missing-receipt boundary"
    Unified.connectomeCarrier
    (Spine.defaultRoleVector "brain-fmri-observation-parent")
    Residual.partial
    Asserted.carrierOnly
    Spine.softInvariant
    (Spine.blockedJProjection "brain/fMRI has no inhabited bridge to literal modular-j authority")
    (Spine.blockedFormalProjectionBundle "brain/fMRI projections are present as blocked non-promoting parent carriers")

canonicalBrainFMRIObjects : List Spine.UnifiedObjectInvariant
canonicalBrainFMRIObjects =
  brainFMRIObject ∷ []

brainFMRIJPromotionBlocked :
  Spine.objectExternalJPromotion brainFMRIObject ≡ false
brainFMRIJPromotionBlocked =
  refl

brainFMRIPostureIsCarrierOnly :
  Spine.proofPosture brainFMRIObject ≡ Asserted.carrierOnly
brainFMRIPostureIsCarrierOnly =
  refl
