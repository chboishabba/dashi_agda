module DASHI.Core.CommonExperimentRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMMON EXPERIMENT REALISATION LANGUAGE
--
-- Repository-native analogue of the common metric-variation language used by
-- the GR/QFT recovery lane.  Candidate models may have different internal
-- control/apparatus coordinates, but a claimed comparison must identify one
-- external experiment and commuting maps into both implementations.
------------------------------------------------------------------------

record CommonExperimentRealisation
    (LeftModel RightModel : Set) : Set₁ where
  constructor commonExperimentRealisation
  field
    Experiment LeftInternal RightInternal Observation : Set

    toLeft : Experiment → LeftInternal
    toRight : Experiment → RightInternal

    observeLeft : LeftModel → LeftInternal → Observation
    observeRight : RightModel → RightInternal → Observation

    experimentReference : Experiment → String
    leftRealisationReference : String
    rightRealisationReference : String
    commonObservationReference : String

open CommonExperimentRealisation public

record CommonExperimentDiscriminator
    {LeftModel RightModel : Set}
    (language : CommonExperimentRealisation LeftModel RightModel)
    (left : LeftModel)
    (right : RightModel) : Set₁ where
  constructor commonExperimentDiscriminator
  field
    experiment : Experiment language
    separates :
      observeLeft language left (toLeft language experiment)
      ≡ observeRight language right (toRight language experiment) → ⊥
    discriminationReference : String

open CommonExperimentDiscriminator public

------------------------------------------------------------------------
-- If the two internal realisations are compared without a common external
-- experiment, there is no theorem here identifying them as the same test.
------------------------------------------------------------------------

record CommonExperimentRealisationBoundary : Set where
  constructor commonExperimentRealisationBoundary
  field
    sameExternalExperimentMayHaveDifferentInternalCoordinates : Bool
    sameExternalExperimentMayHaveDifferentInternalCoordinatesIsTrue :
      sameExternalExperimentMayHaveDifferentInternalCoordinates ≡ true

    independentInternalControlsAutomaticallyMeanSameExperiment : Bool
    independentInternalControlsAutomaticallyMeanSameExperimentIsFalse :
      independentInternalControlsAutomaticallyMeanSameExperiment ≡ false

    commonObservationTypeMakesTwoModelsPhysicallyEquivalent : Bool
    commonObservationTypeMakesTwoModelsPhysicallyEquivalentIsFalse :
      commonObservationTypeMakesTwoModelsPhysicallyEquivalent ≡ false

canonicalCommonExperimentRealisationBoundary :
  CommonExperimentRealisationBoundary
canonicalCommonExperimentRealisationBoundary =
  commonExperimentRealisationBoundary true refl false refl false refl
