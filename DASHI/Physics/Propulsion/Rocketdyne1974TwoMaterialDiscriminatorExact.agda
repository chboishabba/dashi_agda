{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.Rocketdyne1974MaterialIdentityAndConstitutiveDataExact as Mat

------------------------------------------------------------------------
-- HISTORICAL TWO-MATERIAL DISCRIMINATOR
--
-- The final report gives two near-matched extreme-condition observations:
--   Haynes-25: Test 768, about 2.9 O/F, 237 psia, nozzle ~2300 F, damage.
--   WC103:     Test 870-2, 3.01 O/F, 235 psia, rerun of simulated dual
--              oxidizer regulator failure, nozzle reached equilibrium,
--              45 s company-sponsored test without incident.
--
-- The archive therefore contains a genuine empirical material discriminator,
-- but not a perfect single-variable controlled experiment: hardware revision,
-- exact geometry, coating and detailed boundary conditions must stay explicit.
------------------------------------------------------------------------

data ObservedOutcome : Set where
  damaged survivedObservedRun : ObservedOutcome

record HistoricalRun : Set where
  constructor historical-run
  field
    runId : String
    material : Mat.MaterialIdentity
    chamberPressurePsia : Nat
    mixtureRatioHundredths : Nat
    equilibriumNozzleTemperatureF : Nat
    durationSeconds : Nat
    outcome : ObservedOutcome
    sourceReference : String

haynesDamageObserved : HistoricalRun
haynesDamageObserved =
  historical-run "Test 768" Mat.haynes25 237 290 2300 10 damaged
    "NASA-CR-140308 R-9557 p.155; Table 39 context"

wc103FollowupSurvived : HistoricalRun
wc103FollowupSurvived =
  historical-run "Test 870-2" Mat.wc103Columbium 235 301 2300 45 survivedObservedRun
    "NASA-CR-140308 R-9557 Fig.78 p.158; R-9557-1 pp.27-28"

record SameModelRule : Set where
  constructor same-model-rule
  field
    oneThermalModel : Bool
    oneStructuralModelFamily : Bool
    materialAndDocumentedHardwareMayVary : Bool
    postHocModelSwitchForbidden : Bool

sameModelRule : SameModelRule
sameModelRule = same-model-rule true true true true

record ConditionDifference : Set where
  constructor condition-difference
  field
    pressureDifferencePsia : Nat
    mixtureRatioDifferenceHundredths : Nat
    sameReportedEquilibriumNozzleTemperature : Bool
    exactSingleVariableExperiment : Bool
    sourceBoundary : String

historicalConditionDifference : ConditionDifference
historicalConditionDifference =
  condition-difference 2 11 true false
    "235 vs 237 psia and 3.01 vs about 2.90 O/F; hardware/coating identity also differs"

data DiscriminatorLevel : Set where
  archiveOnly empiricalDiscrimination calibratedPrediction : DiscriminatorLevel

record TwoMaterialDiscriminator : Set where
  constructor two-material-discriminator
  field
    rule : SameModelRule
    failedRun : HistoricalRun
    survivedRun : HistoricalRun
    comparison : ConditionDifference
    level : DiscriminatorLevel
    geometryNeededForStressPrediction : Bool
    sameArticleConstitutiveLawNeeded : Bool
    empiricalOutcomeDifferenceEstablished : Bool
    predictiveStressClosureEstablished : Bool

currentDiscriminator : TwoMaterialDiscriminator
currentDiscriminator =
  two-material-discriminator
    sameModelRule
    haynesDamageObserved
    wc103FollowupSurvived
    historicalConditionDifference
    empiricalDiscrimination
    true true true false

record DiscriminatorBoundary : Set where
  constructor discriminator-boundary
  field
    archiveSupportsMaterialOutcomeDiscrimination : Bool
    archiveAloneIdentifiesFailureStress : Bool
    archiveAloneIdentifiesCreepLife : Bool
    rerunIsExactSingleVariableControl : Bool
    sameModelValidationIsStillRequired : Bool

canonicalDiscriminatorBoundary : DiscriminatorBoundary
canonicalDiscriminatorBoundary =
  discriminator-boundary true false false false true
