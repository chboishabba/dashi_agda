module DASHI.Biology.Agriculture.AustralianRestorationSoilFunctionObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES

daguiEtAl2022DOI : String
daguiEtAl2022DOI = "10.1111/rec.13738"

daguiEtAl2022 : Attribution.AttributedSource
daguiEtAl2022 = Attribution.mkDOISource
  "Haylee M. D'Agui; Mieke E. van der Heyde; Paul G. Nevill; Mahsa Mousavi-Derazmahalleh; Kingsley W. Dixon; Benjamin Moreira-Grez; Justin M. Valliere"
  "Evaluating biological properties of topsoil for post-mining ecological restoration: different assessment methods give different results"
  "Restoration Ecology 30(S1):e13738"
  "2022" daguiEtAl2022DOI "https://doi.org/10.1111/rec.13738"
  Attribution.academicArticleSource
  "Seven-mine-site Western Australian comparison of native reference and stockpiled topsoils using microbial-community composition, soil respiration and plant-growth bioassays. Stockpile effects were idiosyncratic/site-specific and different biological measures could disagree; no single biotic measure accurately represented soil functionality as reflected in plant growth."
  Attribution.publicAttribution

data SoilFunctionObserverWorld : Set where
  sameMicrobialTokenHigherPlantFunction : SoilFunctionObserverWorld
  sameMicrobialTokenLowerPlantFunction : SoilFunctionObserverWorld

data SoilFunctionTask : Set where
  plantSupportFunctionTask : SoilFunctionTask

data MicrobialMetricToken : Set where
  sameMicrobialMetric : MicrobialMetricToken

microbialMetricOnly : SoilFunctionObserverWorld → MicrobialMetricToken
microbialMetricOnly _ = sameMicrobialMetric

plantSupportFunction : SoilFunctionTask → SoilFunctionObserverWorld → Bool
plantSupportFunction plantSupportFunctionTask sameMicrobialTokenHigherPlantFunction = true
plantSupportFunction plantSupportFunctionTask sameMicrobialTokenLowerPlantFunction = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

singleMicrobialMetricNotFunctionSufficient :
  LES.TaskFactorisation microbialMetricOnly plantSupportFunction → ⊥
singleMicrobialMetricNotFunctionSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor plantSupportFunctionTask
      {sameMicrobialTokenHigherPlantFunction} {sameMicrobialTokenLowerPlantFunction} refl)

data SoilFunctionObserverRole : Set where
  microbialCommunityCompositionObserver : SoilFunctionObserverRole
  microbialRespirationObserver : SoilFunctionObserverRole
  plantGrowthBioassayObserver : SoilFunctionObserverRole
  stockpileHistoryObserver : SoilFunctionObserverRole

record SoilFunctionObserverBoundary : Set where
  constructor soil-function-observer-boundary
  field
    microbialCompositionAloneDeterminesSoilFunctionality : Bool
    respirationAloneDeterminesPlantGrowthFunctionality : Bool
    anySingleBioticMetricDeterminesSoilFunctionality : Bool
    contradictoryMetricsMayBeCollapsedToOneOutcome : Bool
    oneMineResponseCreatesUniversalTopsoilResponse : Bool
    stockpileDurationAloneDeterminesFunctionalState : Bool
    siteBiomeStockpileAgeAndOriginMustRemainIndexed : Bool
    observerMethodMustRemainIndexed : Bool
    referenceTopsoilAndStockpiledTopsoilAreSameObject : Bool
    observerReceiptCreatesDeploymentAuthority : Bool
open SoilFunctionObserverBoundary public

canonicalSoilFunctionObserverBoundary : SoilFunctionObserverBoundary
canonicalSoilFunctionObserverBoundary = soil-function-observer-boundary
  false false false false false false true true false false

attributionRule : String
attributionRule =
  "D'Agui et al. 2022 (DOI 10.1111/rec.13738) owns its seven-site Western Australian native-reference/stockpiled-topsoil measurements and the empirical finding that different biological assessment methods can yield complex, contradictory and site-specific readings. DASHI owns only the observer-role typing, finite single-metric TaskFactorisation collision and no-promotion boundary. Microbial composition, respiration or any one assay is not promoted to a complete soil-functional state, cross-mine universal law or deployment authority."
