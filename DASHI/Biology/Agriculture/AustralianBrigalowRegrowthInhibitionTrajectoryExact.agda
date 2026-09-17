module DASHI.Biology.Agriculture.AustralianBrigalowRegrowthInhibitionTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryExact as Pioneer
import DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationExact as Grassland

------------------------------------------------------------------------
-- AUSTRALIAN BRIGALOW REGROWTH / INHIBITION TRAJECTORY
------------------------------------------------------------------------

johnsonEtAl2016DOI : String
johnsonEtAl2016DOI = "10.1111/aec.12354"

dwyerMason2018DOI : String
dwyerMason2018DOI = "10.1111/rec.12536"

leBrocqueWagner2018DOI : String
leBrocqueWagner2018DOI = "10.1111/aec.12578"

johnsonEtAl2016 : Attribution.AttributedSource
johnsonEtAl2016 = Attribution.mkDOISource
  "Robert W. Johnson; William J. McDonald; Roderick J. Fensham; Clive A. McAlpine; Michael J. Lawes"
  "Changes over 46 years in plant community structure in a cleared brigalow (Acacia harpophylla) forest"
  "Austral Ecology 41(6):644-656"
  "2016" johnsonEtAl2016DOI "https://doi.org/10.1111/aec.12354"
  Attribution.academicArticleSource
  "Forty-six-year repeated permanent-plot study after brigalow clearing and burning. Acacia harpophylla rapidly regained dominance through root suckering, reached maximum density within two years and then self-thinned; vacant woody niches emerged only after decades. Herbaceous diversity followed a non-monotone trajectory while woody richness increased more steadily. The source is retained as a long-term inhibition/succession record, not a generic law for all Acacia regrowth."
  Attribution.publicAttribution

dwyerMason2018 : Attribution.AttributedSource
dwyerMason2018 = Attribution.mkDOISource
  "John M. Dwyer; Riah Mason"
  "Plant community responses to thinning in densely regenerating Acacia harpophylla forest"
  "Restoration Ecology 26(1):97-105"
  "2018" dwyerMason2018DOI "https://doi.org/10.1111/rec.12536"
  Attribution.academicArticleSource
  "Eight-year randomized thinning experiment in densely resprouting brigalow. Thinning accelerated recruitment of some shrubs and increased some diversity measures, but severe thinning favoured exploitative pioneer-like shrubs and conservative species remained recruitment-limited. Thinning intensity, dispersal and functional composition therefore remain explicit."
  Attribution.publicAttribution

leBrocqueWagner2018 : Attribution.AttributedSource
leBrocqueWagner2018 = Attribution.mkDOISource
  "Andrew F. Le Brocque; Peter M. Wagner"
  "Passive brigalow (Acacia harpophylla) woodland regeneration fails to recover floristic composition in an agricultural landscape"
  "Austral Ecology 43(4):409-423"
  "2018" leBrocqueWagner2018DOI "https://doi.org/10.1111/aec.12578"
  Attribution.academicArticleSource
  "Southern Queensland brigalow regrowth chronosequence including stands older than forty years and remnant references. Older regrowth could approach grazed-remnant stand structure while remaining compositionally distinct from both grazed and ungrazed old-growth remnants; surrounding vegetation, land use, grazing intensity and soil properties correlated with observed states."
  Attribution.publicAttribution

data BrigalowTrajectoryRole : Set where
  rapidRootSuckering : BrigalowTrajectoryRole
  densitySelfThinning : BrigalowTrajectoryRole
  delayedWoodyRecruitment : BrigalowTrajectoryRole
  herbaceousDiversityTrajectory : BrigalowTrajectoryRole
  thinningReleaseTreatment : BrigalowTrajectoryRole
  structuralRecovery : BrigalowTrajectoryRole
  floristicRecovery : BrigalowTrajectoryRole

data BrigalowConsumer : Set where
  stemDensityConsumer : BrigalowConsumer
  woodyRecruitmentConsumer : BrigalowConsumer
  herbaceousRichnessConsumer : BrigalowConsumer
  woodyRichnessConsumer : BrigalowConsumer
  standStructureConsumer : BrigalowConsumer
  floristicCompositionConsumer : BrigalowConsumer
  functionalTraitConsumer : BrigalowConsumer

record BrigalowTrajectoryReceipt : Set where
  constructor brigalow-trajectory-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    temporalReading : String
    interventionReading : String
    consumerReading : String
    boundedReading : String
open BrigalowTrajectoryReceipt public

fortySixYearReceipt : BrigalowTrajectoryReceipt
fortySixYearReceipt = brigalow-trajectory-receipt
  johnsonEtAl2016 johnsonEtAl2016DOI
  "eighteen observations across forty-six years in permanent plots"
  "initial clearing/burning followed by spontaneous brigalow root-sucker regeneration"
  "stem density, canopy cover, species presence and layer-specific diversity trajectories"
  "rapid pioneer dominance, self-thinning and delayed niche release are retained without identifying herbaceous and woody trajectories"

eightYearThinningReceipt : BrigalowTrajectoryReceipt
eightYearThinningReceipt = brigalow-trajectory-receipt
  dwyerMason2018 dwyerMason2018DOI
  "eight years after randomized density-reduction treatments"
  "control versus thinning from about 15,600 stems/ha to 4,000, 2,000 or 1,000 stems/ha"
  "woody recruitment, diversity, composition, size and functional traits"
  "recruitment gains do not by themselves identify reference composition; severe thinning can favour exploitative pioneer-like recruits"

passiveRegrowthReceipt : BrigalowTrajectoryReceipt
passiveRegrowthReceipt = brigalow-trajectory-receipt
  leBrocqueWagner2018 leBrocqueWagner2018DOI
  "regrowth age classes through greater than forty years"
  "passive regeneration in southern Queensland agricultural landscape"
  "stand structure and floristic composition relative to grazed/ungrazed remnants"
  "structural resemblance can precede or occur without floristic equivalence; landscape, grazing and soil context remain indexed"

------------------------------------------------------------------------
-- Finite information-loss witness: stand structure cannot determine flora.
------------------------------------------------------------------------

data RegrowthWorld : Set where
  structurallyRecoveredCompositionDistinct : RegrowthWorld
  structurallyRecoveredCompositionReferenceLike : RegrowthWorld

data StructureToken : Set where
  recoveredStandStructure : StructureToken

data FloristicTask : Set where
  referenceFloristicComposition : FloristicTask

standStructureOnly : RegrowthWorld → StructureToken
standStructureOnly _ = recoveredStandStructure

floristicRecovery : FloristicTask → RegrowthWorld → Bool
floristicRecovery referenceFloristicComposition structurallyRecoveredCompositionDistinct = false
floristicRecovery referenceFloristicComposition structurallyRecoveredCompositionReferenceLike = true

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

standStructureNotTaskSufficientForFloristics :
  LES.TaskFactorisation standStructureOnly floristicRecovery → ⊥
standStructureNotTaskSufficientForFloristics factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor referenceFloristicComposition
      {structurallyRecoveredCompositionReferenceLike}
      {structurallyRecoveredCompositionDistinct} refl)

pioneerBoundaryReused : Pioneer.PioneerDisturbanceBoundary
pioneerBoundaryReused = Pioneer.canonicalPioneerDisturbanceBoundary

grasslandBoundaryReused : Grassland.GrasslandSuccessionBoundary
grasslandBoundaryReused = Grassland.canonicalGrasslandBoundary

record BrigalowBoundary : Set where
  constructor brigalow-boundary
  field
    brigalowRegrowthAbundanceImpliesReleasedSuccession : Bool
    highStemDensityImpliesReferenceCommunity : Bool
    selfThinningImpliesWoodyUnderstoreyRecovery : Bool
    herbaceousAndWoodyDiversityMayBeCollapsed : Bool
    thinningIncreasesRecruitmentImpliesReferenceComposition : Bool
    strongerThinningMonotonicallyImprovesRecovery : Bool
    standStructureRecoveryImpliesFloristicCompositionRecovery : Bool
    oldRegrowthAgeImpliesRemnantEquivalence : Bool
    dispersalLandscapeGrazingAndSoilContextMustRemainIndexed : Bool
    pioneerReleaseImpliesDesiredSuccessionalEndpoint : Bool
    regrowthTrajectoryCreatesDeploymentAuthority : Bool
    syntheticRegrowthWorldsAreSourceMeasurements : Bool
open BrigalowBoundary public

canonicalBrigalowBoundary : BrigalowBoundary
canonicalBrigalowBoundary = brigalow-boundary
  false false false false false false false false true false false false

attributionRule : String
attributionRule =
  "Johnson et al. 2016 (DOI 10.1111/aec.12354) owns its forty-six-year permanent-plot brigalow succession observations. Dwyer & Mason 2018 (DOI 10.1111/rec.12536) owns its randomized eight-year brigalow thinning observations. Le Brocque & Wagner 2018 (DOI 10.1111/aec.12578) owns its southern-Queensland regrowth/remnant structure-composition observations. DASHI owns only the typed inhibition/release/structure/floristics separation, finite stand-structure information-loss witness and no-promotion boundary. Brigalow abundance, thinning response, structural recovery and floristic recovery are not identified, and cross-study results do not create deployment authority."
