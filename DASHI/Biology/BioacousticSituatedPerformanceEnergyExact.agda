module DASHI.Biology.BioacousticSituatedPerformanceEnergyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.SituatedFibreDynamicsEverything as Situated
import DASHI.Physics.Units.SI as SI
import DASHI.Biology.BioacousticSongEnergyExpenditureBidiExact as Energy

------------------------------------------------------------------------
-- SITUATED BIRDSONG PERFORMANCE / ENERGY
--
-- This is a thin application owner over the repository's existing situated-
-- fibre and intersectional nonfactorability machinery.  It preserves acoustic,
-- respiratory, cardiac, movement, energetic and context coordinates as
-- distinct observations over time.  No single coordinate, and no mere product
-- of separately useful coordinates, is promoted to a sufficient explanation
-- of effort, condition, fitness signal or total display cost without an
-- application-supplied factorisation witness.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Primary empirical source roles.
------------------------------------------------------------------------

zollingerAmplitudeSource : Attr.AttributedSource
zollingerAmplitudeSource = Attr.mkDOISource
  "S. A. Zollinger et al."
  "Metabolic and respiratory costs of increasing song amplitude in zebra finches"
  "PLoS ONE 6(9):e23198"
  "2011"
  "10.1371/journal.pone.0023198"
  "https://doi.org/10.1371/journal.pone.0023198"
  Attr.academicArticleSource
  "primary source for amplitude/subsyringeal-pressure coupling and the observed non-coupling to measurable oxygen-consumption increase in that experiment"
  Attr.publicAttribution

franzGollerRespirationSource : Attr.AttributedSource
franzGollerRespirationSource = Attr.mkDOISource
  "Michele Franz; Franz Goller"
  "Respiratory patterns and oxygen consumption in singing zebra finches"
  "Journal of Experimental Biology 206:967-978"
  "2003"
  "10.1242/jeb.00196"
  "https://doi.org/10.1242/jeb.00196"
  Attr.academicArticleSource
  "primary source jointly observing song respiration, airflow, air-sac pressure and oxygen-consumption timing; metabolic increment remains duration/context bounded"
  Attr.publicAttribution

gollerBeakGapeSource : Attr.AttributedSource
gollerBeakGapeSource = Attr.mkDOISource
  "Franz Goller; Mary Jo Mallinckrodt; Sylvia D. Torti"
  "Beak gape dynamics during song in the zebra finch"
  "Journal of Neurobiology 59(3):289-303"
  "2004"
  "10.1002/neu.10327"
  "https://doi.org/10.1002/neu.10327"
  Attr.academicArticleSource
  "primary source for beak-gape covariance with acoustic frequency, air-sac pressure and often sound amplitude; covariance does not establish energetic sufficiency"
  Attr.publicAttribution

cooperGollerHeartRateSource : Attr.AttributedSource
cooperGollerHeartRateSource = Attr.mkDOISource
  "B. G. Cooper; Franz Goller"
  "Physiological insights into the social-context-dependent changes in the rhythm of the song motor program"
  "Journal of Neurophysiology"
  "2006"
  "10.1152/jn.01123.2005"
  "https://doi.org/10.1152/jn.01123.2005"
  Attr.academicArticleSource
  "primary source for heart-rate and respiratory timing differences between directed and undirected zebra-finch song; heart rate is not identical to vocal metabolic expenditure"
  Attr.publicAttribution

otaDanceSource : Attr.AttributedSource
otaDanceSource = Attr.mkDOISource
  "N. Ota et al."
  "Tap dancing birds: the multimodal mutual courtship display of males and females in a socially monogamous songbird"
  "Scientific Reports 5:16614"
  "2015"
  "10.1038/srep16614"
  "https://doi.org/10.1038/srep16614"
  Attr.academicArticleSource
  "primary source for simultaneous singing, bobbing and rapid step-dancing in blue-capped cordon-bleu courtship; movement/display intensity remains distinct from vocal energetic expenditure"
  Attr.publicAttribution

situatedPerformanceSourceAtlas : Attr.AttributedSourceAtlas
situatedPerformanceSourceAtlas = Attr.mkSourceAtlas
  "situated birdsong performance / energy source atlas"
  "DASHI.Biology.BioacousticSituatedPerformanceEnergyExact"
  (zollingerAmplitudeSource ∷ franzGollerRespirationSource ∷
   gollerBeakGapeSource ∷ cooperGollerHeartRateSource ∷
   otaDanceSource ∷ [])
  "source-role atlas for acoustic/respiratory/cardiac/movement/energetic fibres; citations are non-promoting and species/context bounded"

------------------------------------------------------------------------
-- Semantic axes. These are observation classes, not claims that every source
-- measures every coordinate or that the coordinates share one calibration.
------------------------------------------------------------------------

data AcousticAxis : Set where
  pitchFrequency : AcousticAxis
  soundAmplitude : AcousticAxis
  spectralTimbre : AcousticAxis
  breathinessDescriptor : AcousticAxis
  acousticAxisUnresolved : AcousticAxis

data RespiratoryAxis : Set where
  airSacPressure : RespiratoryAxis
  trachealAirflow : RespiratoryAxis
  inspiratoryPhase : RespiratoryAxis
  expiratoryPhase : RespiratoryAxis
  minibreathStructure : RespiratoryAxis
  respiratoryAxisUnresolved : RespiratoryAxis

data CardiacAxis : Set where
  heartRate : CardiacAxis
  cardiacAxisUnresolved : CardiacAxis

data MovementAxis : Set where
  beakGape : MovementAxis
  headBodyMotion : MovementAxis
  stepping : MovementAxis
  bobbing : MovementAxis
  danceDisplay : MovementAxis
  movementAxisUnresolved : MovementAxis

data EnergeticAxis : Set where
  metabolicPower : EnergeticAxis
  respiratoryMechanicalProxy : EnergeticAxis
  acousticRadiatedEnergy : EnergeticAxis
  accumulatedExcessEnergy : EnergeticAxis
  energeticAxisUnresolved : EnergeticAxis

record SituatedContext : Set where
  constructor situated-context
  field
    speciesReference : String
    individualReference : String
    socialContextReference : String
    acousticEnvironmentReference : String
    thermalContextReference : String
    trialReference : String

open SituatedContext public

record SituatedPerformanceState : Set where
  constructor situated-performance-state
  field
    acousticCoordinate : AcousticAxis
    respiratoryCoordinate : RespiratoryAxis
    cardiacCoordinate : CardiacAxis
    movementCoordinate : MovementAxis
    energeticCoordinate : EnergeticAxis
    context : SituatedContext
    physicalTimeReference : String

open SituatedPerformanceState public

powerUnit : SI.Unit SI.Power
powerUnit = Energy.powerUnit

energyUnit : SI.Unit SI.Energy
energyUnit = Energy.energyUnit

situatedMachineryOwner : String
situatedMachineryOwner = "DASHI.Core.SituatedFibreDynamicsEverything"

intersectionalMachineryOwner : String
intersectionalMachineryOwner = "DASHI.Core.IntersectionalNonFactorability"

------------------------------------------------------------------------
-- Consumer-relative calibration debt. These labels do not add a universal
-- score or reorder the existing fly ROI/MaleCNS Pareto frontier.
------------------------------------------------------------------------

data ConsumerCalibrationDebt : Set where
  acousticCalibrationDebt : ConsumerCalibrationDebt
  respiratoryCalibrationDebt : ConsumerCalibrationDebt
  cardiacCalibrationDebt : ConsumerCalibrationDebt
  movementCalibrationDebt : ConsumerCalibrationDebt
  energeticCalibrationDebt : ConsumerCalibrationDebt
  situatedContextDebt : ConsumerCalibrationDebt

consumerCalibrationReading : ConsumerCalibrationDebt → String
consumerCalibrationReading acousticCalibrationDebt =
  "consumer requires a source-bound acoustic calibration such as pitch, SPL or spectral descriptor"
consumerCalibrationReading respiratoryCalibrationDebt =
  "consumer requires source-bound pressure/airflow/phase or other respiratory calibration"
consumerCalibrationReading cardiacCalibrationDebt =
  "consumer requires source-bound heart-rate/cardiophysiological calibration"
consumerCalibrationReading movementCalibrationDebt =
  "consumer requires source-bound beak/body/step/bob/dance movement calibration"
consumerCalibrationReading energeticCalibrationDebt =
  "consumer requires source-bound whole-animal or explicitly named energetic calibration"
consumerCalibrationReading situatedContextDebt =
  "consumer requires species/individual/social/noise/thermal/trial/time context"

consumerDebtDoesNotReorderFlyFrontier : Bool
consumerDebtDoesNotReorderFlyFrontier = true

------------------------------------------------------------------------
-- Finite intersectional witnesses.
--
-- Equal acoustic projection can coexist with different situated effort.
-- Equal energetic projection can coexist with different situated display.
-- Therefore neither flattened axis is sufficient for the richer phenomenon.
------------------------------------------------------------------------

data PerformanceWitnessState : Set where
  sameAcousticLowDemand : PerformanceWitnessState
  sameAcousticHighDemand : PerformanceWitnessState
  sameEnergyStillDisplay : PerformanceWitnessState
  sameEnergyDanceDisplay : PerformanceWitnessState

data AcousticProjection : Set where
  sameAcousticReading : AcousticProjection

data EnergeticProjection : Set where
  sameEnergeticReading : EnergeticProjection

data SituatedEffortOutcome : Set where
  lowerSituatedEffort higherSituatedEffort : SituatedEffortOutcome

data SituatedDisplayOutcome : Set where
  stationarySituatedDisplay dancingSituatedDisplay : SituatedDisplayOutcome

acousticProjection : PerformanceWitnessState → AcousticProjection
acousticProjection sameAcousticLowDemand = sameAcousticReading
acousticProjection sameAcousticHighDemand = sameAcousticReading
acousticProjection sameEnergyStillDisplay = sameAcousticReading
acousticProjection sameEnergyDanceDisplay = sameAcousticReading

situatedEffortOutcome : PerformanceWitnessState → SituatedEffortOutcome
situatedEffortOutcome sameAcousticLowDemand = lowerSituatedEffort
situatedEffortOutcome sameAcousticHighDemand = higherSituatedEffort
situatedEffortOutcome sameEnergyStillDisplay = lowerSituatedEffort
situatedEffortOutcome sameEnergyDanceDisplay = higherSituatedEffort

energeticProjection : PerformanceWitnessState → EnergeticProjection
energeticProjection sameAcousticLowDemand = sameEnergeticReading
energeticProjection sameAcousticHighDemand = sameEnergeticReading
energeticProjection sameEnergyStillDisplay = sameEnergeticReading
energeticProjection sameEnergyDanceDisplay = sameEnergeticReading

situatedDisplayOutcome : PerformanceWitnessState → SituatedDisplayOutcome
situatedDisplayOutcome sameAcousticLowDemand = stationarySituatedDisplay
situatedDisplayOutcome sameAcousticHighDemand = stationarySituatedDisplay
situatedDisplayOutcome sameEnergyStillDisplay = stationarySituatedDisplay
situatedDisplayOutcome sameEnergyDanceDisplay = dancingSituatedDisplay

acousticEffortDiffers :
  situatedEffortOutcome sameAcousticLowDemand ≡
  situatedEffortOutcome sameAcousticHighDemand → ⊥
acousticEffortDiffers ()

energyDisplayDiffers :
  situatedDisplayOutcome sameEnergyStillDisplay ≡
  situatedDisplayOutcome sameEnergyDanceDisplay → ⊥
energyDisplayDiffers ()

acousticSituatedEffortNonFactorability :
  NF.NonFactorabilityWitness acousticProjection situatedEffortOutcome
acousticSituatedEffortNonFactorability = NF.nonFactorabilityWitness
  sameAcousticLowDemand
  sameAcousticHighDemand
  refl
  acousticEffortDiffers

energeticSituatedDisplayNonFactorability :
  NF.NonFactorabilityWitness energeticProjection situatedDisplayOutcome
energeticSituatedDisplayNonFactorability = NF.nonFactorabilityWitness
  sameEnergyStillDisplay
  sameEnergyDanceDisplay
  refl
  energyDisplayDiffers

acousticProjectionCannotDetermineSituatedEffort :
  NF.FactorsThrough acousticProjection situatedEffortOutcome → ⊥
acousticProjectionCannotDetermineSituatedEffort =
  NF.witnessRulesOutEveryFlatFactorisation acousticSituatedEffortNonFactorability

energeticProjectionCannotDetermineSituatedDisplay :
  NF.FactorsThrough energeticProjection situatedDisplayOutcome → ⊥
energeticProjectionCannotDetermineSituatedDisplay =
  NF.witnessRulesOutEveryFlatFactorisation energeticSituatedDisplayNonFactorability

------------------------------------------------------------------------
-- Non-promotion boundaries for the requested axes.
------------------------------------------------------------------------

record SituatedPerformanceBoundary : Set where
  constructor situated-performance-boundary
  field
    pitchAloneDeterminesEnergeticCost : Bool
    amplitudeAloneDeterminesMetabolicCost : Bool
    breathinessAloneDeterminesAirflowOrEnergy : Bool
    respiratoryPressureAloneDeterminesWholeAnimalPower : Bool
    heartRateAloneDeterminesSongProductionCost : Bool
    danceIntensityAloneDeterminesVocalEffort : Bool
    beakGapeAloneDeterminesPitchEnergyOrCondition : Bool
    separateAxesAutoDetermineSituatedPerformance : Bool
    acousticAndEnergeticProductsAutoDetermineFitnessSignal : Bool
    situatedConsumerNeedsFactorisationWitness : Bool
    sourceContextMustRemainRetained : Bool

open SituatedPerformanceBoundary public

canonicalSituatedPerformanceBoundary : SituatedPerformanceBoundary
canonicalSituatedPerformanceBoundary = situated-performance-boundary
  false false false false false false false false false true true

situatedPerformanceReading : String
situatedPerformanceReading =
  "Song/display interpretation is intersectional in the repository's factorisation sense: pitch, amplitude, timbre/breathiness, respiration, heart rate, movement/dance and energetic state may all be useful observers, but none is promoted to total effort, condition, fitness signal or display cost without the situated context and a consumer-specific factorisation witness."
