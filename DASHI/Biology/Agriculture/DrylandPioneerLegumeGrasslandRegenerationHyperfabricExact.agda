module DASHI.Biology.Agriculture.DrylandPioneerLegumeGrasslandRegenerationHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AustralianNativeLegumeRhizobiaRestorationExact as AustralianRhizobia
import DASHI.Biology.Agriculture.AustralianWattleSoilBiotaRehabilitationExact as WattleBiota
import DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationExact as Grassland
import DASHI.Biology.Agriculture.SudangrassNurseCoverCropExact as Sudangrass
import DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationExact as Senegal

------------------------------------------------------------------------
-- COMPARATIVE REGENERATION HYPERFABRIC
--
-- Source systems remain separate.  Only functional roles and consumer
-- requirements are cross-pollinated.
------------------------------------------------------------------------

data RegenerationRole : Set where
  nFixingPioneer : RegenerationRole
  temporaryNurse : RegenerationRole
  soilBiotaCarrier : RegenerationRole
  groundCoverProvider : RegenerationRole
  weedCompetitor : RegenerationRole
  hydrologicalActor : RegenerationRole
  recruitmentFacilitator : RegenerationRole

data RegenerationSystem : Set where
  australianNativeLegumeSystem : RegenerationSystem
  australianMineRehabilitationSystem : RegenerationSystem
  australianGrasslandOldFieldSystem : RegenerationSystem
  sudangrassPastureSystem : RegenerationSystem
  senegaliaDrylandSystem : RegenerationSystem

data TrajectoryWorld : Set where
  earlyFunctionalGainLaterRecovery : TrajectoryWorld
  earlyFunctionalGainLaterFailure : TrajectoryWorld

data TrajectoryTask : Set where
  desiredLongTermRecoveryTask : TrajectoryTask

data EarlySuccessToken : Set where
  earlySuccess : EarlySuccessToken

earlySuccessProjection : TrajectoryWorld → EarlySuccessToken
earlySuccessProjection _ = earlySuccess

trajectorySuccess : TrajectoryTask → TrajectoryWorld → Bool
trajectorySuccess desiredLongTermRecoveryTask earlyFunctionalGainLaterRecovery = true
trajectorySuccess desiredLongTermRecoveryTask earlyFunctionalGainLaterFailure = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

earlySuccessNotTrajectorySufficient : LES.TaskFactorisation earlySuccessProjection trajectorySuccess → ⊥
earlySuccessNotTrajectorySufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor desiredLongTermRecoveryTask
      {earlyFunctionalGainLaterRecovery} {earlyFunctionalGainLaterFailure} refl)

record RegenerationRoleAssignment : Set where
  constructor regeneration-role-assignment
  field
    system : RegenerationSystem
    role : RegenerationRole
    sourceBounded : Bool
open RegenerationRoleAssignment public

australianLegumePioneer : RegenerationRoleAssignment
australianLegumePioneer = regeneration-role-assignment australianNativeLegumeSystem nFixingPioneer true

sudangrassTemporaryNurse : RegenerationRoleAssignment
sudangrassTemporaryNurse = regeneration-role-assignment sudangrassPastureSystem temporaryNurse true

mineSoilBiotaCarrier : RegenerationRoleAssignment
mineSoilBiotaCarrier = regeneration-role-assignment australianMineRehabilitationSystem soilBiotaCarrier true

grasslandRecruitmentFacilitator : RegenerationRoleAssignment
grasslandRecruitmentFacilitator = regeneration-role-assignment australianGrasslandOldFieldSystem recruitmentFacilitator true

senegaliaHydrologicalActor : RegenerationRoleAssignment
senegaliaHydrologicalActor = regeneration-role-assignment senegaliaDrylandSystem hydrologicalActor true

record RegenerationHyperfabricBoundary : Set where
  constructor regeneration-hyperfabric-boundary
  field
    sameFunctionalRoleCreatesSameEcologicalObject : Bool
    sameFunctionalRoleCreatesTransferableResponse : Bool
    sourceSystemIdentityMustRemainIndexed : Bool
    inoculationImpliesCommunityRecovery : Bool
    pioneerEstablishmentImpliesDesiredSuccessionalEndpoint : Bool
    temporaryNurseFunctionImpliesNativeCommunityRecovery : Bool
    soilFunctionImprovementImpliesFloristicRecovery : Bool
    weedSuppressionImpliesBiodiversityRecovery : Bool
    interventionSuccessAtT1ImpliesTrajectorySuccessAtT2 : Bool
    AustralianAcaciaEqualsSenegaliaSenegal : Bool
    agriculturalPastureEqualsNativeGrassland : Bool
    comparativeRoleCreatesDeploymentAuthority : Bool
open RegenerationHyperfabricBoundary public

canonicalRegenerationHyperfabricBoundary : RegenerationHyperfabricBoundary
canonicalRegenerationHyperfabricBoundary = regeneration-hyperfabric-boundary
  false false true false false false false false false false false false

-- Canonical source-bounded lanes are reused, not fused.
australianRhizobiaBoundaryReused : AustralianRhizobia.AustralianRhizobiaBoundary
australianRhizobiaBoundaryReused = AustralianRhizobia.canonicalAustralianRhizobiaBoundary

wattleBiotaBoundaryReused : WattleBiota.WattleSoilBiotaBoundary
wattleBiotaBoundaryReused = WattleBiota.canonicalWattleSoilBiotaBoundary

grasslandBoundaryReused : Grassland.GrasslandSuccessionBoundary
grasslandBoundaryReused = Grassland.canonicalGrasslandBoundary

sudangrassBoundaryReused : Sudangrass.SudangrassBoundary
sudangrassBoundaryReused = Sudangrass.canonicalSudangrassBoundary

attributionRule : String
attributionRule =
  "Australian native-legume, mine-rehabilitation, old-field/grassland, sorghum-sudangrass and Senegalia dryland papers retain ownership of their own empirical propositions. DASHI owns only the comparative role assignments, the finite early-success/long-term-trajectory TaskFactorisation collision and the no-promotion boundary. Shared roles do not create same-object identity, response transfer or deployment authority."
