module DASHI.Physics.Foundations.WavelengthSourceScaleSelectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.ContextConditionedTrajectoryWeightExact as Weight

------------------------------------------------------------------------
-- Generic dimensionless source-scale owner.
--
-- A wavelength/source-size ratio is represented as an exact numerator /
-- denominator coordinate.  Consumers decide how that coordinate maps into
-- a context-dependent mode weighting.  The ratio does not itself alter the
-- admissible trajectory family or imply a stationary/minimum/shortest path.
------------------------------------------------------------------------

record ExactScaleRatio : Set where
  constructor exactScaleRatio
  field
    numeratorScale : Nat
    denominatorScale : Nat

open ExactScaleRatio public

data SourceScaleRole : Set where
  wavelengthOverAperture : SourceScaleRole
  wavelengthOverSource : SourceScaleRole
  reducedWakeWavelengthOverSource : SourceScaleRole
  froudeSquaredCoordinate : SourceScaleRole

data SourceScaleRegime : Set where
  smallRatioRegime : SourceScaleRegime
  orderOneRatioRegime : SourceScaleRegime
  largeRatioRegime : SourceScaleRegime

record SourceScaleCoordinate : Set where
  constructor sourceScaleCoordinate
  field
    role : SourceScaleRole
    ratio : ExactScaleRatio
    regime : SourceScaleRegime
    coordinateReading : String

open SourceScaleCoordinate public

------------------------------------------------------------------------
-- Exact same-coordinate witness for the reduced deep-water wake scale.
--
-- Omitting the conventional 2*pi factor, the characteristic deep-water
-- wavelength scale U^2/g divided by source length L has coordinate
--
--        U^2 / (g L),
--
-- which is exactly the squared Froude coordinate.  Keeping the 2*pi factor
-- belongs to a richer real-valued physical-unit layer and is not fabricated
-- here.
------------------------------------------------------------------------

record ReducedWakeFroudeCoordinate : Set where
  constructor reducedWakeFroudeCoordinate
  field
    speedScaleSquared : Nat
    gravityTimesLengthScale : Nat

    reducedWavelengthRatio : ExactScaleRatio
    froudeSquaredRatio : ExactScaleRatio

    reducedWavelengthRatioIsExact :
      reducedWavelengthRatio
      ≡
      exactScaleRatio speedScaleSquared gravityTimesLengthScale

    froudeSquaredRatioIsExact :
      froudeSquaredRatio
      ≡
      exactScaleRatio speedScaleSquared gravityTimesLengthScale

    sameReducedCoordinate :
      reducedWavelengthRatio ≡ froudeSquaredRatio

open ReducedWakeFroudeCoordinate public

canonicalReducedWakeFroudeCoordinate : ReducedWakeFroudeCoordinate
canonicalReducedWakeFroudeCoordinate =
  reducedWakeFroudeCoordinate
    4
    4
    (exactScaleRatio 4 4)
    (exactScaleRatio 4 4)
    refl
    refl
    refl

------------------------------------------------------------------------
-- Aperture/slit and wake coordinates share a generic mathematical ratio
-- architecture without being identified as the same physical law.
------------------------------------------------------------------------

canonicalApertureScaleCoordinate : SourceScaleCoordinate
canonicalApertureScaleCoordinate =
  sourceScaleCoordinate
    wavelengthOverAperture
    (exactScaleRatio 1 4)
    smallRatioRegime
    "Optical aperture coordinate: wavelength scale over aperture/slit scale; the physical diffraction law remains owned by optics consumers."

canonicalWakeScaleCoordinate : SourceScaleCoordinate
canonicalWakeScaleCoordinate =
  sourceScaleCoordinate
    reducedWakeWavelengthOverSource
    (reducedWavelengthRatio canonicalReducedWakeFroudeCoordinate)
    orderOneRatioRegime
    "Deep-water finite-source wake coordinate: reduced characteristic wavelength scale over source length, sharing the U^2/(gL) coordinate with Fr^2."

apertureRoleAndWakeRoleAreDistinct :
  wavelengthOverAperture ≡ reducedWakeWavelengthOverSource → ⊥
apertureRoleAndWakeRoleAreDistinct ()

------------------------------------------------------------------------
-- Bridge into the existing context-conditioned weighting owner.
------------------------------------------------------------------------

record ScaleConditionedWeightBridge
    (weightSurface : Weight.ContextConditionedTrajectoryWeight) : Set₁ where
  field
    ScaleCoordinate : Set

    scaleCoordinate : ScaleCoordinate → SourceScaleCoordinate
    contextFromScale : ScaleCoordinate → Weight.Context weightSurface

    sameTrajectoryWeightCanDependOnScale :
      Weight.SameTrajectoryContextWeightChange weightSurface

    bridgeReading : String

open ScaleConditionedWeightBridge public

data ToyScaleChoice : Set where
  apertureLikeScale : ToyScaleChoice
  broadExcitationScale : ToyScaleChoice

canonicalScaleConditionedWeightBridge :
  ScaleConditionedWeightBridge Weight.canonicalContextConditionedTrajectoryWeight
canonicalScaleConditionedWeightBridge =
  record
    { ScaleCoordinate = ToyScaleChoice
    ; scaleCoordinate = λ
        { apertureLikeScale → canonicalApertureScaleCoordinate
        ; broadExcitationScale → canonicalWakeScaleCoordinate
        }
    ; contextFromScale = λ
        { apertureLikeScale → Weight.narrowSource
        ; broadExcitationScale → Weight.broadSource
        }
    ; sameTrajectoryWeightCanDependOnScale =
        Weight.canonicalSameTrajectoryContextWeightChange
    ; bridgeReading =
        "A dimensionless source-scale coordinate may select a weighting context on an already-admissible trajectory family; it does not by itself select ontology or change the underlying law."
    }

record WavelengthSourceScaleBoundary : Set where
  constructor wavelengthSourceScaleBoundary
  field
    sameGenericRatioShapeMeansSamePhysicalLaw : Bool
    sameGenericRatioShapeMeansSamePhysicalLawIsFalse :
      sameGenericRatioShapeMeansSamePhysicalLaw ≡ false

    scaleRatioChangesAdmissibilityByDefinition : Bool
    scaleRatioChangesAdmissibilityByDefinitionIsFalse :
      scaleRatioChangesAdmissibilityByDefinition ≡ false

    scaleRatioImpliesStationaryPath : Bool
    scaleRatioImpliesStationaryPathIsFalse :
      scaleRatioImpliesStationaryPath ≡ false

    scaleRatioImpliesMetricShortestPath : Bool
    scaleRatioImpliesMetricShortestPathIsFalse :
      scaleRatioImpliesMetricShortestPath ≡ false

canonicalWavelengthSourceScaleBoundary : WavelengthSourceScaleBoundary
canonicalWavelengthSourceScaleBoundary =
  wavelengthSourceScaleBoundary
    false refl
    false refl
    false refl
    false refl
