module DASHI.Biology.Agriculture.AustralianRestorationMultitrophicTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AustralianRestorationMicrobiomeTrajectoryExact as Microbiome
import DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryExact as Pioneer

------------------------------------------------------------------------
-- AUSTRALIAN MULTI-TROPHIC / LONGITUDINAL RESTORATION TRAJECTORY
------------------------------------------------------------------------

majerNichols1998DOI : String
majerNichols1998DOI = "10.1046/j.1365-2664.1998.00286.x"

majerEtAl2013DOI : String
majerEtAl2013DOI = "10.1186/2192-1709-2-19"

vanDerHeydeEtAl2022DOI : String
vanDerHeydeEtAl2022DOI = "10.1111/mec.16375"

vanDerHeydeEtAl2022PMID : String
vanDerHeydeEtAl2022PMID = "35092102"

majerNichols1998 : Attribution.AttributedSource
majerNichols1998 = Attribution.mkDOISource
  "Jonathan D. Majer; O. G. Nichols"
  "Long-term recolonization patterns of ants in Western Australian rehabilitated bauxite mines with reference to their use as indicators of restoration success"
  "Journal of Applied Ecology 35(1):161-182"
  "1998" majerNichols1998DOI "https://doi.org/10.1046/j.1365-2664.1998.00286.x"
  Attribution.academicArticleSource
  "Four-plot Western Australian bauxite rehabilitation experiment monitored for fourteen years: forest reference, unrevegetated topsoiled plot, tree-planted plot, and mixed-native-seeded plot. Mixed native seeding produced faster early forest-like ant recovery, but treatment differences narrowed later and ant composition still differed from forest. The study explicitly concludes that long-term monitoring reveals information missed by chronosequences."
  Attribution.publicAttribution

majerEtAl2013 : Attribution.AttributedSource
majerEtAl2013 = Attribution.mkDOISource
  "Jonathan D. Majer; Brian Heterick; Thomas Gohr; Elliot Hughes; Lewis Mounsher; Andrew Grigg"
  "Is thirty-seven years sufficient for full return of the ant biota following restoration?"
  "Ecological Processes 2:19"
  "2013" majerEtAl2013DOI "https://doi.org/10.1186/2192-1709-2-19"
  Attribution.academicArticleSource
  "Resampling of the original Western Australian bauxite rehabilitation experiment after roughly thirty-seven years. The initially successful seeded treatment had deteriorated after understorey collapse, the naturally colonised unplanted treatment had improved, all restored plots still differed compositionally from forest, and the forest reference itself changed over time. Diversity recovery is therefore not identified with compositional recovery, early treatment ranking, or a time-invariant reference state."
  Attribution.publicAttribution

vanDerHeydeEtAl2022 : Attribution.AttributedSource
vanDerHeydeEtAl2022 = Attribution.mkDOISource
  "Mieke van der Heyde; Michael Bunce; Kingsley W. Dixon; Kristen Fernandes; Jonathan Majer; Grant Wardell-Johnson; Nicole E. White; Paul Nevill"
  "Evaluating restoration trajectories using DNA metabarcoding of ground-dwelling and airborne invertebrates and associated plant communities"
  "Molecular Ecology 31(7):2172-2188"
  "2022" vanDerHeydeEtAl2022DOI "https://doi.org/10.1111/mec.16375"
  Attribution.academicArticleSource
  "Three-location Western Australian mine-restoration chronosequence using DNA metabarcoding of ground-dwelling and airborne invertebrates together with associated plant-community assays. Ground-dwelling communities gave clearer local restoration signals than airborne communities, and trajectory patterns were inconsistent among locations. Indicator guild, dispersal ability, site and plant community therefore remain explicit coordinates."
  Attribution.publicAttribution

data TrajectoryEvidenceDesign : Set where
  fourteenYearRepeatedMonitoring : TrajectoryEvidenceDesign
  thirtySevenYearSamePlotResampling : TrajectoryEvidenceDesign
  multiSiteChronosequenceMetabarcoding : TrajectoryEvidenceDesign

data TrajectoryConsumer : Set where
  taxonRichnessConsumer : TrajectoryConsumer
  assemblageCompositionConsumer : TrajectoryConsumer
  functionalGroupConsumer : TrajectoryConsumer
  groundFaunaConsumer : TrajectoryConsumer
  airborneFaunaConsumer : TrajectoryConsumer
  plantCommunityConsumer : TrajectoryConsumer
  referenceDistanceConsumer : TrajectoryConsumer

record MultitrophicTrajectoryReceipt : Set where
  constructor multitrophic-trajectory-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    design : TrajectoryEvidenceDesign
    temporalReading : String
    trophicReading : String
    boundedReading : String
open MultitrophicTrajectoryReceipt public

fourteenYearAntReceipt : MultitrophicTrajectoryReceipt
fourteenYearAntReceipt = multitrophic-trajectory-receipt
  majerNichols1998 majerNichols1998DOI fourteenYearRepeatedMonitoring
  "same rehabilitation experiment monitored from establishment through fourteen years"
  "ground-dwelling ant assemblage"
  "early mixed-seeding advantage, later narrowing of treatment differences, and persistent forest-composition difference remain jointly indexed"

thirtySevenYearAntReceipt : MultitrophicTrajectoryReceipt
thirtySevenYearAntReceipt = multitrophic-trajectory-receipt
  majerEtAl2013 majerEtAl2013DOI thirtySevenYearSamePlotResampling
  "same original long-term plots resampled after about thirty-seven years"
  "ant richness, composition and functional groups with vegetation-state context"
  "seeded-treatment regression, unplanted-treatment improvement, persistent reference differences and changing forest reference are retained together"

multitrophicChronosequenceReceipt : MultitrophicTrajectoryReceipt
multitrophicChronosequenceReceipt = multitrophic-trajectory-receipt
  vanDerHeydeEtAl2022 vanDerHeydeEtAl2022DOI multiSiteChronosequenceMetabarcoding
  "restoration-age chronosequences across three Western Australian mine systems"
  "ground-dwelling invertebrates, airborne invertebrates and associated plants"
  "guild mobility, site identity, restoration age and reference community remain explicit; cross-sectional evidence is not promoted to same-plot longitudinal change"

------------------------------------------------------------------------
-- Finite information-loss witness: an early-success scalar cannot answer
-- long-term compositional-trajectory queries.
------------------------------------------------------------------------

data RestorationWorld : Set where
  earlySeededLaterCollapsed : RestorationWorld
  earlySeededLaterPersistent : RestorationWorld

data EarlySuccessToken : Set where
  earlySuccess : EarlySuccessToken

data LongTermTask : Set where
  referenceCompositionTrajectory : LongTermTask

earlySuccessProjection : RestorationWorld → EarlySuccessToken
earlySuccessProjection _ = earlySuccess

longTermTrajectory : LongTermTask → RestorationWorld → Bool
longTermTrajectory referenceCompositionTrajectory earlySeededLaterCollapsed = false
longTermTrajectory referenceCompositionTrajectory earlySeededLaterPersistent = true

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

earlySuccessNotTaskSufficientForLongTermTrajectory :
  LES.TaskFactorisation earlySuccessProjection longTermTrajectory → ⊥
earlySuccessNotTaskSufficientForLongTermTrajectory factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor referenceCompositionTrajectory
      {earlySeededLaterPersistent} {earlySeededLaterCollapsed} refl)

------------------------------------------------------------------------
-- Existing observer/trajectory owners reused without source fusion.
------------------------------------------------------------------------

microbiomeTrajectoryBoundaryReused : Microbiome.MicrobiomeTrajectoryBoundary
microbiomeTrajectoryBoundaryReused = Microbiome.canonicalMicrobiomeTrajectoryBoundary

pioneerTrajectoryBoundaryReused : Pioneer.PioneerDisturbanceBoundary
pioneerTrajectoryBoundaryReused = Pioneer.canonicalPioneerDisturbanceBoundary

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record MultitrophicBoundary : Set where
  constructor multitrophic-boundary
  field
    earlyTreatmentRankingImpliesThirtySevenYearRanking : Bool
    richnessRecoveryImpliesCompositionRecovery : Bool
    functionalGroupRecoveryImpliesCompositionRecovery : Bool
    referenceCommunityMayBeTreatedAsTimeInvariant : Bool
    plantCoverSimilarityImpliesFaunalReferenceConvergence : Bool
    groundFaunaSignalImpliesAirborneFaunaSignal : Bool
    indicatorGuildMobilityMustRemainIndexed : Bool
    siteIdentityMustRemainIndexed : Bool
    chronosequenceCanReplaceLongitudinalObservation : Bool
    referenceChoiceAndReferenceTimeMustRemainIndexed : Bool
    sameAgeAcrossSitesCreatesSameTrajectoryState : Bool
    sourceTrajectoryCreatesDeploymentAuthority : Bool
    syntheticWorldsAreSourceMeasurements : Bool
open MultitrophicBoundary public

canonicalMultitrophicBoundary : MultitrophicBoundary
canonicalMultitrophicBoundary = multitrophic-boundary
  false false false false false false true true false true false false false

attributionRule : String
attributionRule =
  "Majer & Nichols 1998 (DOI 10.1046/j.1365-2664.1998.00286.x) owns its fourteen-year WA bauxite-rehabilitation ant observations and its explicit longitudinal-versus-chronosequence interpretation. Majer et al. 2013 (DOI 10.1186/2192-1709-2-19) owns the thirty-seven-year resampling observations, including deterioration of the initially strong seeded treatment, improvement of naturally colonised treatments, persistent compositional differences, and temporal change in the forest reference. van der Heyde et al. 2022 (DOI 10.1111/mec.16375; PMID 35092102) owns its multi-site WA plant/invertebrate metabarcoding observations and guild-specific restoration signals. DASHI owns only the typed evidence-design separation, finite early-success information-loss witness, and no-promotion boundary. Richness, composition, functional groups, plant state, faunal guilds, restoration age, site and reference time are not collapsed into a single recovery scalar."
