{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.TeslaTowerEmitterMaxCutExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TESLA TOWER EMITTER: FINITE NON-IDENTIFIABILITY AND FREQUENCY LEDGER
--
-- This is a structural proof, not a numerical Maxwell solver, a historical
-- reconstruction, or a biological/quantum-consciousness receiver.
--
-- Reused owners:
--   DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary
--   DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact
--   DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope
--   DASHI.Physics.Foundations.RFCalibrationSourceAtlasExact
--   DASHI.Cognition.QuantumMindRetypingBoundary
------------------------------------------------------------------------

data Contradiction : Set where

data EmissionBranch : Set where
  conventionalRadio : EmissionBranch
  earthIonosphereMode : EmissionBranch
  extendedPotentialHypothesis : EmissionBranch

-- Abstract coupling counterworlds share the same tower height. The physical
-- existence of either is NOT inferred from this finite toy model.
data CouplingWorld : Set where
  zeroCoupling : CouplingWorld
  nonzeroCoupling : CouplingWorld

heightMetres : CouplingWorld → Nat
heightMetres zeroCoupling = 57
heightMetres nonzeroCoupling = 57

data ReceiverSignalClass : Set where
  noReceivedSignal : ReceiverSignalClass
  potentiallyReceivedSignal : ReceiverSignalClass

signalClass : CouplingWorld → ReceiverSignalClass
signalClass zeroCoupling = noReceivedSignal
signalClass nonzeroCoupling = potentiallyReceivedSignal

heightAgrees : heightMetres zeroCoupling ≡ heightMetres nonzeroCoupling
heightAgrees = refl

signalClassesDistinct : noReceivedSignal ≡ potentiallyReceivedSignal → Contradiction
signalClassesDistinct ()

TowerHeightDeterminesSignalClass : Set
TowerHeightDeterminesSignalClass =
  (x y : CouplingWorld) →
  heightMetres x ≡ heightMetres y →
  signalClass x ≡ signalClass y

towerHeightDoesNotDetermineSignal :
  TowerHeightDeterminesSignalClass → Contradiction
towerHeightDoesNotDetermineSignal determines =
  signalClassesDistinct (determines zeroCoupling nonzeroCoupling heightAgrees)

------------------------------------------------------------------------
-- Example linear AM: 100000 Hz carrier, 8 Hz modulation.
-- Source spectrum has fc-fm, fc, fc+fm. The cosine product identity is
-- an analytic modelling premise, NOT proved from Maxwell by this module.
-- A separate LF oscillator or nonlinear mixer is not excluded.
------------------------------------------------------------------------

carrierHz : Nat
carrierHz = 100000

modulationHz : Nat
modulationHz = 8

lowerSidebandHz : Nat
lowerSidebandHz = 99992

upperSidebandHz : Nat
upperSidebandHz = 100008

lowerPlusModulationIsCarrier :
  lowerSidebandHz + modulationHz ≡ carrierHz
lowerPlusModulationIsCarrier = refl

carrierPlusModulationIsUpper :
  carrierHz + modulationHz ≡ upperSidebandHz
carrierPlusModulationIsUpper = refl

data LinearAMFrequencyBin : Set where
  lowerSideband : LinearAMFrequencyBin
  originalCarrier : LinearAMFrequencyBin
  upperSideband : LinearAMFrequencyBin

frequencyHz : LinearAMFrequencyBin → Nat
frequencyHz lowerSideband = lowerSidebandHz
frequencyHz originalCarrier = carrierHz
frequencyHz upperSideband = upperSidebandHz

noDirectEightHzLine :
  (bin : LinearAMFrequencyBin) →
  frequencyHz bin ≡ modulationHz → Contradiction
noDirectEightHzLine lowerSideband ()
noDirectEightHzLine originalCarrier ()
noDirectEightHzLine upperSideband ()

------------------------------------------------------------------------
-- Physics-facing realization socket. Deliberately no concrete instance:
-- Maxwell propagation, drive spectrum, receiver transfer and measured
-- reproducible detection are external obligations, not constructed here.
------------------------------------------------------------------------

record PhysicalTransmitterReceiver : Set₁ where
  field
    SourceState : Set
    MediumField : Set
    ReceiverObservable : Set
    sourceToField : SourceState → MediumField
    fieldToReceiver : MediumField → ReceiverObservable
    sourceSpectrumReference : String
    environmentConstitutiveLawReference : String
    environmentBoundaryConditionReference : String
    fieldPropagationValidationReference : String
    receiverCalibrationReference : String
    independentlyReproducedExperimentReference : String
