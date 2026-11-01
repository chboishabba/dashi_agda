module DASHI.Environment.AcaciaSenegalDrylandTaskFactorisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Acacia

------------------------------------------------------------------------
-- DASHI SYNTHETIC EXTENSION, CALIBRATED BY THE ABAKER ET AL. STUDY
--
-- The paper reports that plantation-age increases in SOC / plant-available
-- water capacity can coexist with lower realised soil moisture than grassland,
-- and that plantations can have more infiltration while also having more ET
-- and less retained soil moisture.  We turn that qualitative separation into
-- finite collision witnesses for the existing LES TaskFactorisation calculus.
--
-- These finite worlds are NOT claimed as additional field observations.
------------------------------------------------------------------------

data DrylandWorld : Set where
  lowerETWorld higherETWorld : DrylandWorld

data MoistureTask : Set where
  retainedMoisture : MoistureTask

soilCarbonOnly : DrylandWorld → Bool
soilCarbonOnly lowerETWorld = true
soilCarbonOnly higherETWorld = true

infiltrationOnly : DrylandWorld → Bool
infiltrationOnly lowerETWorld = true
infiltrationOnly higherETWorld = true

retainedMoistureOutcome : MoistureTask → DrylandWorld → Bool
retainedMoistureOutcome retainedMoisture lowerETWorld = true
retainedMoistureOutcome retainedMoisture higherETWorld = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

soilCarbonOnlyNotTaskSufficient :
  LES.TaskFactorisation soilCarbonOnly retainedMoistureOutcome → ⊥
soilCarbonOnlyNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor retainedMoisture {lowerETWorld} {higherETWorld} refl)

infiltrationOnlyNotTaskSufficient :
  LES.TaskFactorisation infiltrationOnly retainedMoistureOutcome → ⊥
infiltrationOnlyNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor retainedMoisture {lowerETWorld} {higherETWorld} refl)

------------------------------------------------------------------------
-- The repair is not "more trees" or "more carbon"; it is consumer-relative
-- retention of the missing water-balance coordinates.  This record keeps the
-- study's required context explicit without claiming a universal numerical
-- hydrology model.
------------------------------------------------------------------------

record MoistureAdequateProjectionReceipt : Set where
  constructor moisture-adequate-projection-receipt
  field
    soilCarbonRetained : Bool
    hydraulicCapacityRetained : Bool
    runoffRetained : Bool
    infiltrationRetained : Bool
    evapotranspirationRetained : Bool
    drainageRetained : Bool
    rainfallForcingRetained : Bool
    siteIdentityRetained : Bool
    landCoverAndAgeRetained : Bool
    measurementModelRoleRetained : Bool
    sourceBoundaryRetained : Bool

open MoistureAdequateProjectionReceipt public

canonicalMoistureAdequateProjectionReceipt : MoistureAdequateProjectionReceipt
canonicalMoistureAdequateProjectionReceipt =
  moisture-adequate-projection-receipt
    true true true true true true true true true true true

record TaskFactorisationBridgeBoundary : Set where
  constructor task-factorisation-bridge-boundary
  field
    collisionIsFieldObservation : Bool
    collisionIsDASHISyntheticWitness : Bool
    carbonOnlyProjectionAdmittedForMoistureConsumer : Bool
    infiltrationOnlyProjectionAdmittedForMoistureConsumer : Bool
    evapotranspirationCanBeDroppedForMoistureConsumer : Bool
    studyPatternReused : Bool
    canonicalLESFactorisationReused : Bool

open TaskFactorisationBridgeBoundary public

canonicalTaskFactorisationBridgeBoundary : TaskFactorisationBridgeBoundary
canonicalTaskFactorisationBridgeBoundary =
  task-factorisation-bridge-boundary false true false false false true true

studyPatternReused : Acacia.AcaciaStudyPattern
studyPatternReused = Acacia.canonicalStudyPattern
