module DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119FlatSide4CurvatureStressExact as FlatStress
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as Cut
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as Spatial

literalSide4FieldSpatialC3Recovered :
  Cut.literalSide4FieldSpatialC3Recovered ≡ true
literalSide4FieldSpatialC3Recovered = refl

literalSide4CurlSpatialC3Recovered :
  Cut.literalSide4CurlSpatialC3Recovered ≡ true
literalSide4CurlSpatialC3Recovered = refl

literalSide4StressSpatialC3Recovered :
  Cut.literalSide4StressSpatialC3Recovered ≡ true
literalSide4StressSpatialC3Recovered = refl

local01To02StressCovariant : ∀ field site →
  FlatStress.localStressInsertion
    (Cut.spatialC3PhysicalField field)
    (Cut.spatialC3Site site)
    K.component02
  ≡ FlatStress.localStressInsertion field site K.component01
local01To02StressCovariant field site =
  Cut.literalLocalStressSpatialC3Covariant field site K.component01

fieldLevelClassicalC3DoesNotCloseGeneratedActionQ1 :
  Cut.literalSide4FieldC3ClosesFullGeneratedActionQ1 ≡ false
fieldLevelClassicalC3DoesNotCloseGeneratedActionQ1 = refl
