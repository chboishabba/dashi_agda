module DASHI.Geology.SaltBidiRegressionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Geology.SaltGeochemistryExact as Salt
import DASHI.Geology.SaltConservationSpineExact as Spine
import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact as Water
import DASHI.Chemistry.DrinkingWaterChloramineDBPBoundaryExact as Combined
import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact as Distribution
import DASHI.Chemistry.DrinkingWaterChloramineNitrificationBiofilmBidiExact as Nitrification
import DASHI.Chemistry.DrinkingWaterCorrosionMetalReleaseExact as Metal
import DASHI.Chemistry.DrinkingWaterTapMetalObservationBidiExact as TapMetal
import DASHI.Environment.RootSoilSaltLineageBidiExact as RootSalt

------------------------------------------------------------------------
-- Regression surface for the salt cross-domain programme.
-- These are structural anti-collapse checks, not empirical claims.
------------------------------------------------------------------------

record SaltBidiRegression : Set where
  constructor saltBidiRegression
  field
    brineNotPromotedToPureNaCl :
      Salt.brineIsPureNaClSolution Salt.canonicalSaltGeochemistryBoundary ≡ false

    labelsDoNotProveLineage :
      Spine.sameSpeciesLabelProvesSameMaterialLineage
        Spine.canonicalSaltConservationBoundary ≡ false

    geologicalSaltNotDirectDisinfectant :
      Industry.geologicalSaltDirectlyDisinfectsTapWater
        Industry.canonicalChlorAlkaliBoundary ≡ false

    rootSodiumDoesNotRecoverSource :
      RootSalt.rootSodiumObservationIdentifiesGeologicalSaltSource
        RootSalt.canonicalRootSoilSaltBoundary ≡ false

    rootChlorideDoesNotRecoverSource :
      RootSalt.rootChlorideObservationIdentifiesGeologicalSaltSource
        RootSalt.canonicalRootSoilSaltBoundary ≡ false

    chlorineAddedNotMeasuredResidual :
      Water.chlorineAddedEqualsMeasuredFreeResidual
        Water.canonicalDrinkingWaterChlorineSpeciationBoundary ≡ false

    doseDoesNotFixHOClFractionWithoutPH :
      Water.chlorineDoseDeterminesHOClFractionWithoutPH
        Water.canonicalDrinkingWaterChlorineSpeciationBoundary ≡ false

    residualDoesNotProvePerformance :
      Water.freeChlorineResidualProvesDisinfectionPerformance
        Water.canonicalDrinkingWaterChlorineSpeciationBoundary ≡ false

    freeResidualNotCombinedResidual :
      Combined.freeResidualEqualsCombinedResidual
        Combined.canonicalDrinkingWaterCombinedChlorineBoundary ≡ false

    exposureAloneDoesNotDetermineDBPYield :
      Combined.chlorineExposureWithoutPrecursorsDeterminesDBPYield
        Combined.canonicalDrinkingWaterCombinedChlorineBoundary ≡ false

    plantResidualNotTapResidual :
      Distribution.treatmentPlantResidualEqualsTapResidual
        Distribution.canonicalDistributionResidualCorrosionBoundary ≡ false

    chlorideDoesNotUniquelyCauseCorrosion :
      Distribution.chloridePresenceAloneProvesCorrosionCause
        Distribution.canonicalDistributionResidualCorrosionBoundary ≡ false

    tapResidualDoesNotRecoverHistory :
      Distribution.tapResidualRecoversTreatmentAndDistributionHistory
        Distribution.canonicalDistributionResidualCorrosionBoundary ≡ false

    lowChloramineDoesNotProveNitrification :
      Nitrification.lowChloramineResidualProvesNitrification
        Nitrification.canonicalChloramineNitrificationBiofilmBoundary ≡ false

    biofilmDoesNotProvePathogenPresence :
      Nitrification.biofilmPresenceProvesPathogenPresence
        Nitrification.canonicalChloramineNitrificationBiofilmBoundary ≡ false

    metalDoesNotRecoverUniqueSourceMaterial :
      Metal.metalDetectionIdentifiesUniqueSourceMaterial
        Metal.canonicalCorrosionMetalReleaseBoundary ≡ false

    metalDoesNotRecoverUniqueReleaseMechanism :
      Metal.metalDetectionIdentifiesUniqueReleaseMechanism
        Metal.canonicalCorrosionMetalReleaseBoundary ≡ false

    firstDrawNotSameObservationLanguageAsFlushed :
      TapMetal.firstDrawEqualsFlushedObservationLanguage
        TapMetal.canonicalTapMetalObservationBoundary ≡ false

    oneSampleDoesNotRecoverHydraulicHistory :
      TapMetal.oneSampleRecoversStagnationAndHydraulicHistory
        TapMetal.canonicalTapMetalObservationBoundary ≡ false

    lowDissolvedDoesNotProveLowTotalMetal :
      TapMetal.lowDissolvedMetalProvesLowParticulateAndTotalMetal
        TapMetal.canonicalTapMetalObservationBoundary ≡ false

canonicalSaltBidiRegression : SaltBidiRegression
canonicalSaltBidiRegression =
  saltBidiRegression
    refl refl refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl refl refl refl refl
