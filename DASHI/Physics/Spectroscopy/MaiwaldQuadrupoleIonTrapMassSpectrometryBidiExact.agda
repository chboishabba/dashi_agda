module DASHI.Physics.Spectroscopy.MaiwaldQuadrupoleIonTrapMassSpectrometryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.InverseProblemIdentifiabilityBidiExact as Inv

------------------------------------------------------------------------
-- Maiwald et al. / JPL quadrupole ion-trap mass-spectrometry lane.
-- Source examples:
-- * Belousov et al., Sampling Accelerated Micron Scale Ice Particles with a
--   Quadrupole Ion Trap Mass Spectrometer, JASMS (2021), DOI 10.1021/jasms.0c00442.
-- * Maiwald et al., Compact High Resolution QIT-Mass Spectrometers for Lunar
--   and Planetary Applications, EGU2020-3177.
------------------------------------------------------------------------

data QITStage : Set where
  particleEncounter sampleCapture ionProduction ionTrap massAnalysis speciesInference : QITStage


data QITObservable : Set where
  massToCharge peakIntensity peakWidth fragmentationPattern : QITObservable

record PlanetaryQITExperiment : Set where
  constructor planetary-qit-experiment
  field
    targetMedium : String
    instrumentClass : String
    observables : List QITObservable
    samplingInterface : String
    calibrationReference : String
    sourceReference : String

open PlanetaryQITExperiment public

enceladusIceParticleLane : PlanetaryQITExperiment
enceladusIceParticleLane = planetary-qit-experiment
  "accelerated micron-scale ice particles / plume analogue"
  "Paul quadrupole ion-trap mass spectrometer"
  (massToCharge ∷ peakIntensity ∷ peakWidth ∷ [])
  "particle capture/impact and conversion into trapped analyte ions"
  "mass-axis, trapping-field, detector-response and sampling-efficiency calibration"
  "Belousov et al. 2021, DOI 10.1021/jasms.0c00442; Frank Maiwald coauthor"

record QITBoundary : Set where
  constructor qit-boundary
  field
    massToChargePeakUniquelyIdentifiesMolecule : Bool
    massToChargePeakUniquelyIdentifiesMoleculeIsFalse :
      massToChargePeakUniquelyIdentifiesMolecule ≡ false
    samplingEfficiencyIsAutomaticallyUnity : Bool
    samplingEfficiencyIsAutomaticallyUnityIsFalse :
      samplingEfficiencyIsAutomaticallyUnity ≡ false
    laboratoryIceParticleCaptureAutomaticallyEqualsFlightPlumeSampling : Bool
    laboratoryIceParticleCaptureAutomaticallyEqualsFlightPlumeSamplingIsFalse :
      laboratoryIceParticleCaptureAutomaticallyEqualsFlightPlumeSampling ≡ false
    fragmentationCanProvideAdditionalChemicalDiscrimination : Bool
    fragmentationCanProvideAdditionalChemicalDiscriminationIsTrue :
      fragmentationCanProvideAdditionalChemicalDiscrimination ≡ true

canonicalQITBoundary : QITBoundary
canonicalQITBoundary = qit-boundary false refl false refl false refl true refl

maiwaldQITReverse : Inv.InverseProblemReverseObligation
maiwaldQITReverse = Inv.inverse-problem-reverse-obligation
  "planetary quadrupole ion-trap mass spectrometry"
  "chemical composition of sampled ice/plume material"
  "mass-to-charge spectrum and ion-count pattern"
  "mass scale, trapping field, detector efficiency and particle-sampling transfer calibration"
  "sampling + ionisation/trapping + mass-analysis response model"
  "isobars/isomers and sampling/ionisation efficiencies can produce ambiguous spectra"
  "fragmentation / orthogonal spectroscopy / repeated sampling channel"
