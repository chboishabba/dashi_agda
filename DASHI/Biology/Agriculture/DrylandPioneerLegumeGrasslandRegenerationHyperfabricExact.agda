module DASHI.Biology.Agriculture.DrylandPioneerLegumeGrasslandRegenerationHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AustralianNativeLegumeRhizobiaRestorationExact as AustralianRhizobia
import DASHI.Biology.Agriculture.AustralianWattleSoilBiotaRehabilitationExact as WattleBiota
import DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationExact as Grassland
import DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryExact as Pioneer
import DASHI.Biology.Agriculture.AustralianRestorationMicrobiomeTrajectoryExact as Microbiome
import DASHI.Biology.Agriculture.SudangrassNurseCoverCropExact as Sudangrass
import DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationExact as Senegal
import DASHI.Biology.Agriculture.QueenslandLeyBNFCarryoverExact as QueenslandLey
import DASHI.Biology.Agriculture.QueenslandWoodyLegumeGrassNitrogenCyclingExact as QueenslandWoodyGrass
import DASHI.Biology.Agriculture.QueenslandDesmanthusGrassBNFInteractionExact as QueenslandDesmanthus

------------------------------------------------------------------------
-- COMPARATIVE REGENERATION HYPERFABRIC
--
-- Source systems remain separate. Only functional roles, observer semantics,
-- transport semantics and trajectory requirements are cross-pollinated.
------------------------------------------------------------------------

data RegenerationRole : Set where
  nFixingPioneer : RegenerationRole
  temporaryNurse : RegenerationRole
  soilBiotaCarrier : RegenerationRole
  groundCoverProvider : RegenerationRole
  weedCompetitor : RegenerationRole
  hydrologicalActor : RegenerationRole
  recruitmentFacilitator : RegenerationRole
  disturbanceResponsivePioneer : RegenerationRole
  microbiomeTrajectoryIndicator : RegenerationRole
  nitrogenCarryoverComparator : RegenerationRole
  nitrogenTransportCarrier : RegenerationRole
  competitionMediatedBNFContext : RegenerationRole

data RegenerationSystem : Set where
  australianNativeLegumeSystem : RegenerationSystem
  australianMineRehabilitationSystem : RegenerationSystem
  australianGrasslandOldFieldSystem : RegenerationSystem
  australianAcaciaPioneerSystem : RegenerationSystem
  australianRestorationMicrobiomeSystem : RegenerationSystem
  sudangrassPastureSystem : RegenerationSystem
  senegaliaDrylandSystem : RegenerationSystem
  queenslandLeyCarryoverSystem : RegenerationSystem
  queenslandWoodyLegumeGrassSystem : RegenerationSystem
  queenslandDesmanthusGrassSystem : RegenerationSystem

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

australianAcaciaDisturbancePioneer : RegenerationRoleAssignment
australianAcaciaDisturbancePioneer = regeneration-role-assignment australianAcaciaPioneerSystem disturbanceResponsivePioneer true

australianMicrobiomeIndicator : RegenerationRoleAssignment
australianMicrobiomeIndicator = regeneration-role-assignment australianRestorationMicrobiomeSystem microbiomeTrajectoryIndicator true

senegaliaHydrologicalActor : RegenerationRoleAssignment
senegaliaHydrologicalActor = regeneration-role-assignment senegaliaDrylandSystem hydrologicalActor true

queenslandLeyCarryoverComparator : RegenerationRoleAssignment
queenslandLeyCarryoverComparator = regeneration-role-assignment queenslandLeyCarryoverSystem nitrogenCarryoverComparator true

queenslandWoodyGrassTransportCarrier : RegenerationRoleAssignment
queenslandWoodyGrassTransportCarrier = regeneration-role-assignment queenslandWoodyLegumeGrassSystem nitrogenTransportCarrier true

queenslandDesmanthusInteractionContext : RegenerationRoleAssignment
queenslandDesmanthusInteractionContext = regeneration-role-assignment queenslandDesmanthusGrassSystem competitionMediatedBNFContext true

record RegenerationHyperfabricBoundary : Set where
  constructor regeneration-hyperfabric-boundary
  field
    sameFunctionalRoleCreatesSameEcologicalObject : Bool
    sameFunctionalRoleCreatesTransferableResponse : Bool
    sourceSystemIdentityMustRemainIndexed : Bool
    inoculationImpliesCommunityRecovery : Bool
    pioneerEstablishmentImpliesDesiredSuccessionalEndpoint : Bool
    pioneerDominanceImpliesSuccessfulSuccessionalRelease : Bool
    referenceLikeRichnessImpliesReferenceLikeComposition : Bool
    disturbanceRegimeMustRemainIndexed : Bool
    temporaryNurseFunctionImpliesNativeCommunityRecovery : Bool
    soilFunctionImprovementImpliesFloristicRecovery : Bool
    weedSuppressionImpliesBiodiversityRecovery : Bool
    chronosequenceAgeGradientImpliesLongitudinalCausalRecovery : Bool
    microbiomeReferenceSimilarityImpliesWholeEcosystemRecovery : Bool
    interventionSuccessAtT1ImpliesTrajectorySuccessAtT2 : Bool
    AustralianAcaciaEqualsSenegaliaSenegal : Bool
    agriculturalPastureEqualsNativeGrassland : Bool
    comparativeRoleCreatesDeploymentAuthority : Bool
    fixedNitrogenImpliesSameDownstreamNitrogenRoute : Bool
    residueMediatedTransferImpliesLivingRootTransfer : Bool
    grassCompetitionHasContextFreeSign : Bool
    nitrogenServiceCanBeOptimisedWithoutWaterState : Bool
    queenslandPastureComparatorCreatesAcaciaSameObjectEvidence : Bool
    explicitCounterfactualRequiredForFertilizerReplacement : Bool
open RegenerationHyperfabricBoundary public

canonicalRegenerationHyperfabricBoundary : RegenerationHyperfabricBoundary
canonicalRegenerationHyperfabricBoundary = regeneration-hyperfabric-boundary
  false false true false false false false true false false false false false false false false false
  false false false false false true

-- Canonical source-bounded lanes are reused, not fused.
australianRhizobiaBoundaryReused : AustralianRhizobia.AustralianRhizobiaBoundary
australianRhizobiaBoundaryReused = AustralianRhizobia.canonicalAustralianRhizobiaBoundary

wattleBiotaBoundaryReused : WattleBiota.WattleSoilBiotaBoundary
wattleBiotaBoundaryReused = WattleBiota.canonicalWattleSoilBiotaBoundary

grasslandBoundaryReused : Grassland.GrasslandSuccessionBoundary
grasslandBoundaryReused = Grassland.canonicalGrasslandBoundary

pioneerBoundaryReused : Pioneer.PioneerTrajectoryBoundary
pioneerBoundaryReused = Pioneer.canonicalPioneerTrajectoryBoundary

microbiomeBoundaryReused : Microbiome.MicrobiomeTrajectoryBoundary
microbiomeBoundaryReused = Microbiome.canonicalMicrobiomeTrajectoryBoundary

sudangrassBoundaryReused : Sudangrass.SudangrassBoundary
sudangrassBoundaryReused = Sudangrass.canonicalSudangrassBoundary

queenslandLeyBoundaryReused : QueenslandLey.QueenslandLeyBoundary
queenslandLeyBoundaryReused = QueenslandLey.canonicalQueenslandLeyBoundary

queenslandWoodyGrassBoundaryReused : QueenslandWoodyGrass.WoodyLegumeGrassBoundary
queenslandWoodyGrassBoundaryReused = QueenslandWoodyGrass.canonicalWoodyLegumeGrassBoundary

queenslandDesmanthusBoundaryReused : QueenslandDesmanthus.DesmanthusBoundary
queenslandDesmanthusBoundaryReused = QueenslandDesmanthus.canonicalDesmanthusBoundary

attributionRule : String
attributionRule =
  "Australian native-legume, mine-rehabilitation, old-field/grassland, Acacia-pioneer/disturbance, restoration-microbiome, sorghum-sudangrass, Senegalia dryland, Queensland ley-carryover, Queensland woody-legume/grass and Queensland Desmanthus papers retain ownership of their own empirical propositions. DASHI owns only the comparative role assignments, observer/trajectory/transport separations, the finite early-success/long-term-trajectory TaskFactorisation collision and the no-promotion boundary. Shared roles, fixed-N labels, reference-like richness, chronosequence age gradients or microbiome similarity do not create same-object identity, response transfer, a unique N-transfer route, causal recovery, whole-ecosystem recovery or deployment authority. Queensland residue transfer does not become living-root transfer; Desmanthus grass interaction has no context-free sign; ley N service cannot erase water state; and a quantified fertilizer-replacement claim retains its explicit mineral-N counterfactual requirement. Queensland agricultural comparators do not manufacture Acacia/Senegalia same-object evidence."
