module DASHI.Biology.Agriculture.AustralianRestorationMicrobiomeTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

gellieEtAl2017DOI : String
gellieEtAl2017DOI = "10.1111/mec.14081"

ngugiEtAl2018DOI : String
ngugiEtAl2018DOI = "10.1111/rec.12631"

lemEtAl2022DOI : String
lemEtAl2022DOI = "10.1111/rec.13635"

peddleEtAl2023DOI : String
peddleEtAl2023DOI = "10.1111/rec.13706"

gellieEtAl2017 : Attribution.AttributedSource
gellieEtAl2017 = Attribution.mkDOISource
  "Nicholas J. C. Gellie; Jacob G. Mills; Martin F. Breed; Andrew J. Lowe"
  "Revegetation rewilds the soil bacterial microbiome of an old field"
  "Molecular Ecology 26(11):2895-2904"
  "2017" gellieEtAl2017DOI "https://doi.org/10.1111/mec.14081"
  Attribution.academicArticleSource
  "South Australian old-field revegetation source. Soil bacterial composition differed with revegetation age; older revegetated sites were more similar to remnant stands than younger/cleared sites. Retained as cross-sectional reference-similarity evidence, not a longitudinal causal law."
  Attribution.publicAttribution

ngugiEtAl2018 : Attribution.AttributedSource
ngugiEtAl2018 = Attribution.mkDOISource
  "Michael R. Ngugi; Paul G. Dennis; Victor J. Neldner; David Doley; Nigel Fechner; Andrew McElnea"
  "Open-cut mining impacts on soil abiotic and bacterial community properties as shown by restoration chronosequence"
  "Restoration Ecology 26(5):839-850"
  "2018" ngugiEtAl2018DOI "https://doi.org/10.1111/rec.12631"
  Attribution.academicArticleSource
  "Subtropical Queensland coal-mine restoration chronosequence spanning 3-23 years. Bacterial composition became more similar to nonmined analogues with age while richness/evenness could exceed reference and total carbon recovery was projected on a longer timescale."
  Attribution.publicAttribution

lemEtAl2022 : Attribution.AttributedSource
lemEtAl2022 = Attribution.mkDOISource
  "Alfie J. Lem; Craig Liddicoat; Andrew Bissett; Christian Cando-Dumancela; Michael G. Gardner; Shawn D. Peddle; Carl D. Watson; Martin F. Breed"
  "Does revegetation cause soil microbiota recovery? Evidence from revisiting a revegetation chronosequence 6 years after initial sampling"
  "Restoration Ecology 30(8):e13635"
  "2022" lemEtAl2022DOI "https://doi.org/10.1111/rec.13635"
  Attribution.academicArticleSource
  "South Australian longitudinal revisit of a revegetation chronosequence at two timepoints six years apart. The expected additional bacterial convergence toward reference was not observed; spatial soil chemistry, biotic/abiotic barriers, sampling season and reference-site variability remain candidate explanations."
  Attribution.publicAttribution

peddleEtAl2023 : Attribution.AttributedSource
peddleEtAl2023 = Attribution.mkDOISource
  "Shawn D. Peddle; Andrew Bissett; R. J. Borrett; P. Bullock; Michael G. Gardner; Craig Liddicoat; Mark Tibbett; Martin F. Breed; Siegfried L. Krauss"
  "Soil DNA chronosequence analysis shows bacterial community re-assembly following post-mining forest rehabilitation"
  "Restoration Ecology 31(3):e13706"
  "2023" peddleEtAl2023DOI "https://doi.org/10.1111/rec.13706"
  Attribution.academicArticleSource
  "Western Australian bauxite-mine 28-year rehabilitation chronosequence. Bacterial community composition changed strongly and generally approached unmined reference with rehabilitation age while alpha diversity did not itself distinguish reference from rehabilitation."
  Attribution.publicAttribution

data MicrobiomeStudyDesign : Set where
  crossSectionalChronosequence : MicrobiomeStudyDesign
  repeatedLongitudinalSampling : MicrobiomeStudyDesign

data MicrobiomeEvidenceRole : Set where
  referenceSimilarityTrend : MicrobiomeEvidenceRole
  alphaDiversityObservation : MicrobiomeEvidenceRole
  communityCompositionObservation : MicrobiomeEvidenceRole
  longitudinalChangeObservation : MicrobiomeEvidenceRole

record MicrobiomeTrajectoryReceipt : Set where
  constructor microbiome-trajectory-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    design : MicrobiomeStudyDesign
    role : MicrobiomeEvidenceRole
    temporalReading : String
    boundedReading : String
open MicrobiomeTrajectoryReceipt public

lemLongitudinalReceipt : MicrobiomeTrajectoryReceipt
lemLongitudinalReceipt = microbiome-trajectory-receipt
  lemEtAl2022 lemEtAl2022DOI repeatedLongitudinalSampling longitudinalChangeObservation
  "same restoration chronosequence revisited after six years"
  "absence of expected additional convergence blocks promotion from cross-sectional age pattern to a causal longitudinal recovery law"

ngugiChronosequenceReceipt : MicrobiomeTrajectoryReceipt
ngugiChronosequenceReceipt = microbiome-trajectory-receipt
  ngugiEtAl2018 ngugiEtAl2018DOI crossSectionalChronosequence referenceSimilarityTrend
  "3-23 year rehabilitation chronosequence"
  "reference similarity, alpha diversity, vegetation and soil chemistry remain separate consumers"

record MicrobiomeTrajectoryBoundary : Set where
  constructor microbiome-trajectory-boundary
  field
    chronosequenceSimilarityImpliesLongitudinalCausalRecovery : Bool
    restorationAgeImpliesObservedWithinSiteChange : Bool
    alphaDiversityRecoveryImpliesCommunityCompositionRecovery : Bool
    microbiomeReferenceSimilarityImpliesWholeEcosystemRecovery : Bool
    crossStudyReferenceSimilarityCreatesSameEmpiricalObject : Bool
    samplingSeasonSoilChemistryAndReferenceChoiceMustRemainIndexed : Bool
    plantRevegetationAndMicrobiomeStateMustRemainJointlyObservedForCausalClaim : Bool
    microbiomeTrajectoryCreatesDeploymentAuthority : Bool
open MicrobiomeTrajectoryBoundary public

canonicalMicrobiomeTrajectoryBoundary : MicrobiomeTrajectoryBoundary
canonicalMicrobiomeTrajectoryBoundary = microbiome-trajectory-boundary
  false false false false false true true false

attributionRule : String
attributionRule =
  "Gellie et al. 2017 (DOI 10.1111/mec.14081), Ngugi et al. 2018 (DOI 10.1111/rec.12631), Lem et al. 2022 (DOI 10.1111/rec.13635) and Peddle et al. 2023 (DOI 10.1111/rec.13706) own their respective Australian restoration microbiome observations. DASHI owns only the typed separation between cross-sectional chronosequence evidence, longitudinal change, alpha diversity, composition and causal-recovery claims. Cross-study similarity trends do not create same-object identity or deployment authority."
