module DASHI.Visual.CameraDirectorExact where

open import DASHI.Core.Prelude

data CameraMode : Set where
  fitActiveSemanticRegion : CameraMode
  programmeOverview : CameraMode

record CameraDirective : Set where
  constructor cameraDirective
  field
    cameraProgramme : String
    cameraFocusNodeIds : List String
    cameraMode : CameraMode
    cameraReason : String

open CameraDirective public

record CameraDirectorBoundary : Set where
  constructor cameraDirectorBoundary
  field
    cameraMayChooseSemanticAuthority : Bool
    cameraMayChooseSemanticAuthorityIsFalse :
      cameraMayChooseSemanticAuthority ≡ false

    cameraMayReturnToExistingProgrammeRegion : Bool
    cameraMayReturnToExistingProgrammeRegionIsTrue :
      cameraMayReturnToExistingProgrammeRegion ≡ true

    cameraShouldFitActiveSemanticSet : Bool
    cameraShouldFitActiveSemanticSetIsTrue :
      cameraShouldFitActiveSemanticSet ≡ true

canonicalCameraDirectorBoundary : CameraDirectorBoundary
canonicalCameraDirectorBoundary =
  cameraDirectorBoundary
    false refl
    true refl
    true refl
