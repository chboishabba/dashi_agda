module DASHI.Cognition.EpsteinPsychedelicNeuroforecastingCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Cognition.EpsteinPsychedelicNetworkEvidenceExact as Epstein

------------------------------------------------------------------------
-- NEUROFORECASTING x EPSTEIN/YU BEHAVIOUR-RESEARCH CROSS-POLLINATION
--
-- Methodology source:
--   Kosuke Motoki, Shinsuke Suzuki, Ryuta Kawashima, Motoaki Sugiura (2020),
--   "A Combination of Self-Reported Data and Social-Related Neural Measures
--    Forecasts Viral Marketing Success on Social Media",
--   Journal of Interactive Marketing 52:99-117,
--   DOI 10.1016/j.intmar.2020.06.003.
--
-- Independent Yu background source:
--   WIRED (2017), "Inside Silicon Valley's new non-religion: consciousness
--   hacking", profiles Gino Yu as using interactive media/VR plus EEG and fMRI
--   in consciousness research.  This establishes background capability/context,
--   not use of those methods in an Epstein-funded programme.
------------------------------------------------------------------------

data PlatformSurface : Set where
  facebookVideoAds : PlatformSurface
  instagramContent : PlatformSurface
  unspecifiedSocialMedia : PlatformSurface

data PredictionDirection : Set where
  stimulusToBrain : PredictionDirection
  brainToAggregateOutcome : PredictionDirection
  stimulusBrainToAggregateSharing : PredictionDirection
  brainToIndividualControl : PredictionDirection

record NeuroforecastingSourceReceipt : Set where
  constructor neuroforecasting-source-receipt
  field
    authors : String
    title : String
    doi : String
    participantCount : Nat
    stimulusPlatform : PlatformSurface
    usesFMRI : Bool
    socialRelatedNeuralMeasureForecastsAggregateSharing : Bool
    subjectiveShareIntentionAloneForecastsAggregateSharing : Bool
    combinedModelImprovesForecast : Bool
    metaAuthored : Bool
    instagramDeploymentEstablished : Bool
open NeuroforecastingSourceReceipt public

motoki2020Receipt : NeuroforecastingSourceReceipt
motoki2020Receipt = neuroforecasting-source-receipt
  "Kosuke Motoki; Shinsuke Suzuki; Ryuta Kawashima; Motoaki Sugiura"
  "A Combination of Self-Reported Data and Social-Related Neural Measures Forecasts Viral Marketing Success on Social Media"
  "10.1016/j.intmar.2020.06.003"
  40 facebookVideoAds true true false true false false

record PredictionDirectionReceipt : Set where
  constructor prediction-direction-receipt
  field
    direction : PredictionDirection
    coarseFMRIObserverReused : Bool
    aggregateOutcomeTarget : Bool
    individualBehaviourControlTarget : Bool
open PredictionDirectionReceipt public

motokiDirectionReceipt : PredictionDirectionReceipt
motokiDirectionReceipt = prediction-direction-receipt
  stimulusBrainToAggregateSharing true true false

-- Existing repo observer discipline remains live: an fMRI-like observation is
-- many-to-one and does not recover the microscopic activation state.
fmriObserverBoundary : Neural.NeuralLaplacianBoundary
fmriObserverBoundary = Neural.canonicalNeuralLaplacianBoundary

------------------------------------------------------------------------
-- Independent Yu technical-background receipt.
------------------------------------------------------------------------

record YuNeurotechBackgroundReceipt : Set where
  constructor yu-neurotech-background-receipt
  field
    source : String
    interactiveMediaReported : Bool
    virtualRealityReported : Bool
    EEGReported : Bool
    fMRIReported : Bool
    epsteinFundedUseEstablished : Bool
    neuroforecastingUseEstablished : Bool
open YuNeurotechBackgroundReceipt public

ginoYuIndependentNeurotechBackground : YuNeurotechBackgroundReceipt
ginoYuIndependentNeurotechBackground = yu-neurotech-background-receipt
  "WIRED 2017 consciousness-hacking profile"
  true true true true false false

------------------------------------------------------------------------
-- Cross-pollination with the Epstein/Yu tranche.
------------------------------------------------------------------------

record EpsteinYuNeuroforecastingComparison : Set where
  constructor epstein-yu-neuroforecasting-comparison
  field
    yuCommunityProposalExists : Bool
    yuBehaviourLanguagePresent : Bool
    yuIndependentEEGFMRIBackground : Bool
    validatedNeuroforecastingUseByEpsteinYu : Bool
    validatedFMRIProgrammeByEpsteinYu : Bool
    populationForecastingEqualsBehaviourControl : Bool
    methodologyTransferEstablished : Bool
open EpsteinYuNeuroforecastingComparison public

currentComparison : EpsteinYuNeuroforecastingComparison
currentComparison = epstein-yu-neuroforecasting-comparison
  true true true false false false false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS.
------------------------------------------------------------------------

data ForecastEstablishesMechanism : Set where
data FacebookResultEstablishesInstagramDeployment : Set where
data NeuroforecastingEstablishesEpsteinYuUse : Set where
data BackgroundEstablishesEpsteinFundedUse : Set where
data AggregatePredictionEstablishesIndividualControl : Set where
data FMRIObservationRecoversMicroscopicState : Set where

forecastDoesNotEstablishMechanism : ForecastEstablishesMechanism → ⊥
forecastDoesNotEstablishMechanism ()

facebookResultDoesNotEstablishInstagramDeployment :
  FacebookResultEstablishesInstagramDeployment → ⊥
facebookResultDoesNotEstablishInstagramDeployment ()

neuroforecastingDoesNotEstablishEpsteinYuUse :
  NeuroforecastingEstablishesEpsteinYuUse → ⊥
neuroforecastingDoesNotEstablishEpsteinYuUse ()

backgroundDoesNotEstablishEpsteinFundedUse :
  BackgroundEstablishesEpsteinFundedUse → ⊥
backgroundDoesNotEstablishEpsteinFundedUse ()

aggregatePredictionDoesNotEstablishIndividualControl :
  AggregatePredictionEstablishesIndividualControl → ⊥
aggregatePredictionDoesNotEstablishIndividualControl ()

fmriObservationDoesNotRecoverMicroscopicState :
  FMRIObservationRecoversMicroscopicState → ⊥
fmriObservationDoesNotRecoverMicroscopicState ()

record NeuroforecastingCrossPollinationBoundary : Set where
  constructor neuroforecasting-cross-pollination-boundary
  field
    facebookStimulusSurfaceRetained : Bool
    instagramDeploymentPaid : Bool
    metaAuthorshipPaid : Bool
    aggregateForecastingRetained : Bool
    yuEEGFMRIBackgroundRetained : Bool
    individualControlPaid : Bool
    epsteinYuMethodTransferPaid : Bool
    coarseFMRIObserverBoundaryRetained : Bool

canonicalNeuroforecastingCrossPollinationBoundary :
  NeuroforecastingCrossPollinationBoundary
canonicalNeuroforecastingCrossPollinationBoundary =
  neuroforecasting-cross-pollination-boundary
    true false false true true false false true
