module DASHI.Culture.MissingDeceasedTwentyScientistScienceSourceDataReplayBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.ExoticGravity.NingLiYBCOSourceDataReplayExact as Ning
import DASHI.Physics.Materials.ZhouGuangyuanAerogelProcessPropertyDataReplayExact as Zhou
import DASHI.Physics.Planetary.HicksSmallBodyPhotometryDataReplayExact as Hicks
import DASHI.Biology.JasonThomasAssayDataReplayExact as Thomas
import DASHI.Control.ZhangDaibingControlDataReplayExact as Zhang
import DASHI.GameTheory.FengYangheClassificationDataReplayExact as Feng

------------------------------------------------------------------------
-- ROUND-14 SOURCE-DATA BIDI ADAPTER
--
-- The adapter deliberately separates numeric source data from bounded source
-- coordinates whose row-level payload is still unavailable.  Neither class
-- pays historical deployment, custody, programme identity or event cause.
------------------------------------------------------------------------

data SourceDataReplayState : Set where
  numericSourceData : SourceDataReplayState
  boundedSourceCoordinates : SourceDataReplayState
  blockedOnRowLevelData : SourceDataReplayState

data SourceDataReplayWitness : Set where
  ningData : Ning.NingSourceDataReplay → SourceDataReplayWitness
  zhouData : Zhou.ZhouProcessPropertyDataReplay → SourceDataReplayWitness
  hicksData : Hicks.HicksPhotometryDataReplay → SourceDataReplayWitness
  thomasData : Thomas.ThomasAssayDataReplay → SourceDataReplayWitness
  zhangData : Zhang.ZhangDaibingControlDataReplay → SourceDataReplayWitness
  fengData : Feng.FengClassificationDataReplay → SourceDataReplayWitness

record SourceDataReplayBinding : Set where
  constructor source-data-replay-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    replayState : SourceDataReplayState
    witness : SourceDataReplayWitness
    pays : String
    stillBlockedOn : String

open SourceDataReplayBinding public

ningBinding : SourceDataReplayBinding
ningBinding = source-data-replay-binding
  "Ning Li" B.ningLiFibre numericSourceData
  (ningData Ning.ningSourceDataReplay)
  "static acceleration bound plus rotating-field geometry/drive coordinates"
  "later AC Gravity/Army same-object apparatus, calibration, controls and result table"

zhouBinding : SourceDataReplayBinding
zhouBinding = source-data-replay-binding
  "Zhou Guangyuan" B.zhouGuangyuanFibre numericSourceData
  (zhouData Zhou.zhouProcessPropertyDataReplay)
  "named PI-D1/PI-A4 sample and finite process/property coordinates"
  "complete sample table, uncertainty, processing recipe and scale-up window"

hicksBinding : SourceDataReplayBinding
hicksBinding = source-data-replay-binding
  "Michael David Hicks" B.michaelHicksFibre boundedSourceCoordinates
  (hicksData Hicks.hicksPhotometryDataReplay)
  "campaign/date/observatory/2.4 h period and radar-consistency coordinates"
  "Hicks raw lightcurve, viewing geometry and photometric calibration"

thomasBinding : SourceDataReplayBinding
thomasBinding = source-data-replay-binding
  "Jason R. Thomas" B.jasonThomasFibre boundedSourceCoordinates
  (thomasData Thomas.thomasAssayDataReplay)
  "assay cell/readout topology, PRAK candidate and PIK-III/NCOA4/FTH1 coordinates"
  "per-well screen matrix, dose-response arrays and proteomics table"

zhangBinding : SourceDataReplayBinding
zhangBinding = source-data-replay-binding
  "Zhang Daibing" B.zhangDaibingFibre boundedSourceCoordinates
  (zhangData Zhang.zhangDaibingControlDataReplay)
  "DFC/multi-surface/PSO/disturbance/objective architecture"
  "vehicle model, controller gains, disturbance PSDs and touchdown-dispersion series"

fengBinding : SourceDataReplayBinding
fengBinding = source-data-replay-binding
  "Feng Yanghe" B.fengYangheFibre blockedOnRowLevelData
  (fengData Feng.fengClassificationDataReplay)
  "publisher-exact multinomial/Dirichlet and filtering/sampling workflow coordinates"
  "book equations, example dataset, noise parameters and classifier outputs"

sourceDataReplayBindings : List SourceDataReplayBinding
sourceDataReplayBindings =
  ningBinding ∷ zhouBinding ∷ hicksBinding ∷ thomasBinding ∷ zhangBinding ∷ fengBinding ∷ []

sourceDataReplayBindingsCount : Nat
sourceDataReplayBindingsCount = 6

numericSourceDataAndBlockedRowsRemainDistinct : Bool
numericSourceDataAndBlockedRowsRemainDistinct = true

sourceDataBindingDoesNotPayHistoricalUse : Bool
sourceDataBindingDoesNotPayHistoricalUse = false

sourceDataBindingDoesNotPayCustody : Bool
sourceDataBindingDoesNotPayCustody = false

sourceDataBindingDoesNotPayCommonProgramme : Bool
sourceDataBindingDoesNotPayCommonProgramme = false

sourceDataBindingCanRefineExecutionPareto : Bool
sourceDataBindingCanRefineExecutionPareto = true
