module DASHI.Biology.BioacousticSongEnergyExpenditureBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Environment.LESResearchCrossPollinationRound4Exact as LES
import DASHI.Physics.Units.SI as SI
import DASHI.Biology.BioacousticFlySnowballParetoBidiExact as Base
import DASHI.Biology.BioacousticFlySIUnitSnowballParetoBidiExact as Units

------------------------------------------------------------------------
-- BIRDSONG ENERGY EXPENDITURE
--
-- LES supplies the governance rule that real experiment cost/outcome models
-- remain empirical inputs. SI supplies Power/Energy dimensions and units.
-- This owner specializes those surfaces to song without manufacturing an
-- energetic law from formal structure alone.
------------------------------------------------------------------------

oberwegerGollerSource : Attr.AttributedSource
oberwegerGollerSource = Attr.mkDOISource
  "K. Oberweger; F. Goller"
  "The metabolic cost of birdsong production"
  "Journal of Experimental Biology 204(19):3379-3388"
  "2001"
  "10.1242/jeb.204.19.3379"
  "https://doi.org/10.1242/jeb.204.19.3379"
  Attr.academicArticleSource
  "primary respirometry source for whole-animal oxygen-consumption cost of song across zebra finch, canary and starling"
  Attr.publicAttribution

wardSpeakmanSlaterSource : Attr.AttributedSource
wardSpeakmanSlaterSource = Attr.mkDOISource
  "S. Ward; J. R. Speakman; P. J. B. Slater"
  "The energy cost of song in the canary, Serinus canaria"
  "Animal Behaviour 66(5):893-902"
  "2003"
  "10.1006/anbe.2003.2250"
  "https://doi.org/10.1006/anbe.2003.2250"
  Attr.academicArticleSource
  "primary respirometry source for canary song metabolic rate relative to quiet standing and basal metabolism"
  Attr.publicAttribution

wardSlaterHeatTransferSource : Attr.AttributedSource
wardSlaterHeatTransferSource = Attr.mkDOISource
  "S. Ward; P. J. B. Slater"
  "Heat transfer and the energetic cost of singing by canaries Serinus canaria"
  "Journal of Comparative Physiology A 191(10):953-964"
  "2005"
  "10.1007/s00359-005-0022-4"
  "https://doi.org/10.1007/s00359-005-0022-4"
  Attr.academicArticleSource
  "primary thermal-model source for whole-animal metabolic power during singing versus standing"
  Attr.publicAttribution

zollingerAmplitudeSource : Attr.AttributedSource
zollingerAmplitudeSource = Attr.mkDOISource
  "S. A. Zollinger et al."
  "Metabolic and respiratory costs of increasing song amplitude in zebra finches"
  "PLoS ONE 6(9):e23198"
  "2011"
  "10.1371/journal.pone.0023198"
  "https://doi.org/10.1371/journal.pone.0023198"
  Attr.academicArticleSource
  "primary source separating increased subsyringeal pressure from measurable whole-animal oxygen-consumption increase"
  Attr.publicAttribution

songEnergySourceAtlas : Attr.AttributedSourceAtlas
songEnergySourceAtlas = Attr.mkSourceAtlas
  "birdsong energy expenditure empirical source atlas"
  "DASHI.Biology.BioacousticSongEnergyExpenditureBidiExact"
  (oberwegerGollerSource ∷ wardSpeakmanSlaterSource ∷
   wardSlaterHeatTransferSource ∷ zollingerAmplitudeSource ∷ [])
  "empirical calibration and fibre-separation sources; citation neither imports proof nor creates biological authority"

------------------------------------------------------------------------
-- LES external-cost boundary.
------------------------------------------------------------------------

realExperimentCostAndOutcomeModelsStillExternal : Bool
realExperimentCostAndOutcomeModelsStillExternal =
  LES.realExperimentCostAndOutcomeModelsStillExternal
    LES.canonicalLESRound4RemainingScientificFrontier

realExperimentCostAndOutcomeModelsStillExternalIsTrue :
  realExperimentCostAndOutcomeModelsStillExternal ≡ true
realExperimentCostAndOutcomeModelsStillExternalIsTrue = refl

------------------------------------------------------------------------
-- SI power / energy carriers.
--
-- Ward & Slater 2005: singing 0.70 +/- 0.02 W, standing 0.62 +/- 0.02 W.
-- centiScale makes the exact fixed-point carrier 70 and 62 respectively.
------------------------------------------------------------------------

canaryStandingPower : SI.Measurement SI.Power SI.centiScale
canaryStandingPower = SI.measurement
  (SI.posQ 62)
  2
  SI.watt
  "Ward & Slater 2005; DOI 10.1007/s00359-005-0022-4"
  "reported standing metabolic power 0.62 +/- 0.02 W"

canarySingingPower : SI.Measurement SI.Power SI.centiScale
canarySingingPower = SI.measurement
  (SI.posQ 70)
  2
  SI.watt
  "Ward & Slater 2005; DOI 10.1007/s00359-005-0022-4"
  "reported singing metabolic power 0.70 +/- 0.02 W"

powerUnit : SI.Unit SI.Power
powerUnit = SI.watt

energyUnit : SI.Unit SI.Energy
energyUnit = SI.joule

record SongEnergyInterval : Set₁ where
  constructor song-energy-interval
  field
    baselinePower : SI.Measurement SI.Power SI.centiScale
    singingPower : SI.Measurement SI.Power SI.centiScale
    intervalReference : String
    integrationRuleReference : String
    resultingEnergyDimension : SI.Dimension
    resultingEnergyUnit : SI.Unit resultingEnergyDimension
    empiricalCalibrationRequired : Bool

open SongEnergyInterval public

canonicalCanarySongEnergyInterval : SongEnergyInterval
canonicalCanarySongEnergyInterval = song-energy-interval
  canaryStandingPower
  canarySingingPower
  "song interval [t0,t1] must come from a source-bound temporal carrier"
  "E_song_excess = integral_[t0,t1] (P_song(t) - P_baseline(t)) dt; numeric integration is empirical/runtime work"
  SI.Energy
  SI.joule
  true

------------------------------------------------------------------------
-- Non-collapse across energetic fibres.
------------------------------------------------------------------------

data SongEnergeticFibre : Set where
  wholeAnimalMetabolicPower : SongEnergeticFibre
  respiratorySyringealMechanicalProxy : SongEnergeticFibre
  acousticRadiatedEnergy : SongEnergeticFibre
  opportunityCost : SongEnergeticFibre
  dailyEnergyBudgetCost : SongEnergeticFibre

fibreReading : SongEnergeticFibre → String
fibreReading wholeAnimalMetabolicPower =
  "whole-animal metabolic power measured/estimated by respirometry or heat-transfer modelling"
fibreReading respiratorySyringealMechanicalProxy =
  "respiratory/syringeal pressure, airflow or muscle-work proxy; not automatically whole-animal metabolic power"
fibreReading acousticRadiatedEnergy =
  "radiated acoustic energy; not automatically metabolic or respiratory mechanical expenditure"
fibreReading opportunityCost =
  "forgone alternative activity/foraging/rest opportunity; requires a declared ecological consumer model"
fibreReading dailyEnergyBudgetCost =
  "contribution to daily energy expenditure/budget; requires activity duration and ecological calibration"

record SongEnergyBoundary : Set where
  constructor song-energy-boundary
  field
    acousticEnergyEqualsMetabolicEnergy : Bool
    respiratoryPressureEqualsMetabolicPower : Bool
    louderSongImpliesHigherWholeAnimalMetabolicPower : Bool
    songPowerEqualsExcessSongEnergy : Bool
    metabolicIncrementEqualsFitnessCost : Bool
    sourceRatioTransfersAcrossSpecies : Bool
    LESFormalismCreatesEmpiricalCostModel : Bool
    unitCorrectnessCreatesEmpiricalCalibration : Bool
    intervalIntegrationNeedsTemporalCarrier : Bool
    empiricalCostMayRemainConsumerRelative : Bool

open SongEnergyBoundary public

canonicalSongEnergyBoundary : SongEnergyBoundary
canonicalSongEnergyBoundary = song-energy-boundary
  false false false false false false false false true true

------------------------------------------------------------------------
-- Bidi rule: evidence may pay a bounded energetic claim; downstream consumers
-- reopen the exact calibration/time/species/context dependency they require.
------------------------------------------------------------------------

record SongEnergyBidiReceipt : Set where
  constructor song-energy-bidi-receipt
  field
    forwardEvidenceReference : String
    forwardBoundedClaim : String
    reverseReopeningCondition : String
    reverseDependency : String
    sourceIdentityRetained : Bool
    unitSemanticsRetained : Bool
    speciesContextRetained : Bool
    measurementMethodRetained : Bool
    citationCreatesAuthority : Bool

open SongEnergyBidiReceipt public

canaryThermalPowerBidi : SongEnergyBidiReceipt
canaryThermalPowerBidi = song-energy-bidi-receipt
  "Ward & Slater 2005 DOI 10.1007/s00359-005-0022-4: 0.70 +/- 0.02 W singing versus 0.62 +/- 0.02 W standing"
  "for the measured canary context, singing whole-animal metabolic power exceeded standing by the reported thermal-model estimate"
  "different species, temperature/activity context, measurement method, baseline state or song interval"
  "empirical metabolic-power calibration for the consumer's actual bird/context"
  true true true true false

zebraFinchAmplitudeBidi : SongEnergyBidiReceipt
zebraFinchAmplitudeBidi = song-energy-bidi-receipt
  "Zollinger et al. 2011 DOI 10.1371/journal.pone.0023198"
  "higher song amplitude required higher subsyringeal pressure but did not produce a measurable oxygen-consumption increase in that experiment"
  "consumer attempts to infer whole-animal metabolic cost from acoustic amplitude or respiratory pressure alone"
  "direct metabolic calibration or separately justified mechanical-to-metabolic model"
  true true true true false

------------------------------------------------------------------------
-- Eighth Pareto coordinate. The seven-axis SI owner remains authoritative for
-- identity/alignment/provenance/opportunity/risk/implementation/unit debt.
------------------------------------------------------------------------

data EnergyExtendedAxis : Set where
  inheritedAxis : Units.SIExtendedFrontierAxis → EnergyExtendedAxis
  energeticCostDebt : EnergyExtendedAxis

axisReference : EnergyExtendedAxis → String
axisReference (inheritedAxis axis) = Units.axisReference axis
axisReference energeticCostDebt =
  "unpaid empirical energetic calibration needed by a consumer interpreting song, behaviour or physiology as an energy cost"

leafCost : EnergyExtendedAxis → Base.FrontierLeaf → Nat
leafCost (inheritedAxis axis) leaf = Units.leafCost axis leaf
leafCost energeticCostDebt Base.exactExternalManifest = 0
leafCost energeticCostDebt Base.sameTrialStimulusFunctionalTimebase = 0
leafCost energeticCostDebt Base.roiTrialPlaneIdentity = 0
leafCost energeticCostDebt Base.functionalToMaleCNSRegistration = 0
leafCost energeticCostDebt Base.rendererPolish = 4

energyExtendedFrontierProblem : Pareto.ConsumerMDLProblem
energyExtendedFrontierProblem = Pareto.consumerMDLProblem
  Base.FrontierLeaf
  (λ _ → ⊤)
  (λ _ → ⊤)
  (leafCost (inheritedAxis Units.implementationCost))
  _≡_
  Base.leafReference
  "application-declared ordinal axes; energetic calibration remains independent of identity, provenance, unit and implementation debt"
  "retain energetic-cost debt for consumers that make energetic claims; do not scalarise it into general alpha"

energyExtendedFrontierCosts : Pareto.CostHyperfabric energyExtendedFrontierProblem
energyExtendedFrontierCosts = Pareto.costHyperfabric EnergyExtendedAxis leafCost axisReference

energyExtendedFrontierView : NDim.NDimParetoView energyExtendedFrontierCosts
energyExtendedFrontierView = NDim.ndimParetoView
  8
  "seven inherited debt/risk/cost/unit axes plus energetic-cost debt"
  axisReference
  true
  "energetic-cost debt is consumer-relative and must not be collapsed into unit correctness or implementation cost"

currentInspectionFrontier : List Base.FrontierLeaf
currentInspectionFrontier = Units.currentInspectionFrontier

firstExecutionLeaf : Base.FrontierLeaf
firstExecutionLeaf = Units.firstExecutionLeaf

------------------------------------------------------------------------
-- Current interpretation.
------------------------------------------------------------------------

currentSongEnergyReading : String
currentSongEnergyReading =
  "Birdsong energy is a calibrated empirical fibre. Whole-animal metabolic power, respiratory/syringeal mechanics, radiated acoustic energy, opportunity cost and daily energy-budget cost remain distinct. SI supplies watt/joule semantics; LES says the real cost model remains external; the attribution snowball retains species/method/context; and the eighth Pareto coordinate records energetic debt only for consumers that actually require an energy-cost interpretation."
