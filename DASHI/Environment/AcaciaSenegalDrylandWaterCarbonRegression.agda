module DASHI.Environment.AcaciaSenegalDrylandWaterCarbonRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Acacia
import DASHI.Environment.AcaciaSenegalDrylandTaskFactorisationExact as Task

------------------------------------------------------------------------
-- Regression surface: the source-bounded study bridge must preserve the
-- separate carbon, hydraulic-capacity, soil-moisture and water-balance axes,
-- and the LES task-sufficiency collisions must remain live.
------------------------------------------------------------------------

_sourceDOI-pinned : Acacia.primaryStudyDOI ≡ "10.1016/j.jaridenv.2017.12.004"
_sourceDOI-pinned = refl

_SOC-age-trend-paid : Acacia.soilOrganicCarbonIncreasesWithPlantationAge Acacia.canonicalStudyPattern ≡ true
_SOC-age-trend-paid = refl

_PAWC-age-trend-paid : Acacia.plantAvailableWaterCapacityIncreasesWithPlantationAge Acacia.canonicalStudyPattern ≡ true
_PAWC-age-trend-paid = refl

_plantation-moisture-age-trend-paid : Acacia.plantationSoilMoistureIncreasesWithAge Acacia.canonicalStudyPattern ≡ true
_plantation-moisture-age-trend-paid = refl

_grassland-still-wetter-paid : Acacia.grasslandSoilMoistureHigherThanPlantations Acacia.canonicalStudyPattern ≡ true
_grassland-still-wetter-paid = refl

_plantation-runoff-lower-paid : Acacia.plantationRunoffLower Acacia.canonicalStudyPattern ≡ true
_plantation-runoff-lower-paid = refl

_plantation-infiltration-higher-paid : Acacia.plantationInfiltrationHigher Acacia.canonicalStudyPattern ≡ true
_plantation-infiltration-higher-paid = refl

_plantation-ET-higher-paid : Acacia.plantationEvapotranspirationHigher Acacia.canonicalStudyPattern ≡ true
_plantation-ET-higher-paid = refl

_plantation-drainage-lower-paid : Acacia.plantationDrainageLower Acacia.canonicalStudyPattern ≡ true
_plantation-drainage-lower-paid = refl

_SOC-does-not-close-moisture : Acacia.soilCarbonAloneDeterminesSoilMoisture Acacia.canonicalAcaciaBoundary ≡ false
_SOC-does-not-close-moisture = refl

_infiltration-does-not-close-moisture : Acacia.infiltrationAloneDeterminesRetainedSoilMoisture Acacia.canonicalAcaciaBoundary ≡ false
_infiltration-does-not-close-moisture = refl

_tree-cover-does-not-imply-wetter : Acacia.moreTreeCoverAutomaticallyMeansWetterSoil Acacia.canonicalAcaciaBoundary ≡ false
_tree-cover-does-not-imply-wetter = refl

_single-metric-restoration-ranking-blocked : Acacia.singleMetricAutomaticallyRanksRestorationSuccess Acacia.canonicalAcaciaBoundary ≡ false
_single-metric-restoration-ranking-blocked = refl

_source-does-not-authorise-deployment : Acacia.studyAutomaticallyAuthorisesDrylandTreePlanting Acacia.canonicalAcaciaBoundary ≡ false
_source-does-not-authorise-deployment = refl

_carbon-only-collision-is-synthetic : Task.collisionIsDASHISyntheticWitness Task.canonicalTaskFactorisationBridgeBoundary ≡ true
_carbon-only-collision-is-synthetic = refl

_carbon-only-not-admitted-for-moisture : Task.carbonOnlyProjectionAdmittedForMoistureConsumer Task.canonicalTaskFactorisationBridgeBoundary ≡ false
_carbon-only-not-admitted-for-moisture = refl

_infiltration-only-not-admitted-for-moisture : Task.infiltrationOnlyProjectionAdmittedForMoistureConsumer Task.canonicalTaskFactorisationBridgeBoundary ≡ false
_infiltration-only-not-admitted-for-moisture = refl

_ET-retained-in-repair : Task.evapotranspirationRetained Task.canonicalMoistureAdequateProjectionReceipt ≡ true
_ET-retained-in-repair = refl
