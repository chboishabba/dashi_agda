module DASHI.Chemistry.HydrogenFuelCycleDeviceEvidenceExact where

-- Provenance: existing DASHI.Chemistry.TransitionKernel distinguishes
-- patentDisclosed, directlyMeasured and other evidence stages; source roles
-- are not collapsed. The experiment design is user-directed, ChatGPT-drafted
-- (2026-11-09); vendor assertions do not establish any physical effect.
--
-- All electrical/thermal quantities below are input ENERGY over the same
-- measurement window, not instant power. These energy amounts are not
-- portable between device architectures.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Chemistry.IndustrialReactiveEnergyBalanceExact as Ledger
import DASHI.Chemistry.HydrogenFuelCycleIntervalBoundsExact as Interval
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Physics.Units.SI as SI

-- The constructors prevent an intake retrofit from inheriting a
-- plasma-membrane heating load from historical, unrelated patent machinery.
data ModeAuxiliaries : Ledger.DeviceMode → Set where
  intakeAux :
    (electrolysis controls compression : Nat) →
    ModeAuxiliaries Ledger.intakeElectrolysis
  plasmaAux :
    (plasma heater separation controls compression : Nat) →
    ModeAuxiliaries Ledger.plasmaMembrane
  synthesisAux :
    (electrolysis capture synthesis separation controls : Nat) →
    ModeAuxiliaries Ledger.carbonSynthesis

totalModeAux :
  ∀ {mode} → ModeAuxiliaries mode → Nat
totalModeAux (intakeAux electrolyser controls compression) =
  electrolyser + controls + compression
totalModeAux (plasmaAux plasma heater separation controls compression) =
  plasma + heater + separation + controls + compression
totalModeAux (synthesisAux electrolysis capture synthesis separation controls) =
  electrolysis + capture + synthesis + separation + controls

-- The lab records which source of energy pays the auxiliary burden.
-- Fuel-fired heat is a separate chemical feed, not electricity.
record DeviceTestReceipt (mode : Ledger.DeviceMode) : Set₁ where
  field
    auxiliaries : ModeAuxiliaries mode
    measuredElectricityJoules : SI.Measurement SI.Energy SI.unitScale
    fuelFiredProcessHeatJoules : SI.Measurement SI.Energy SI.unitScale
    heatRecoveryMetered : Set
    startupAndShutdownInventoryMetered : Set
    inputSourceAndInstrumentCalibration : Set
    allLoadsSameIntegrationWindow : Set
    auxiliaryEnergyCompleteness : Set

open DeviceTestReceipt public

data TestArm : Set where
  dieselBaseline : TestArm
  poweredButNoGas : TestArm
  externallyMeteredHydrogen : TestArm
  oxygenOnly : TestArm
  fullRetrofit : TestArm

record EngineRun : Set₁ where
  field
    testArm : TestArm
    loadAndSpeed : String
    timestampAndDuration : String
    dieselMassRate : SI.Measurement SI.Mass SI.unitScale
    netOutputEnergy : SI.Measurement SI.Energy SI.unitScale
    externalElectricity : SI.Measurement SI.Energy SI.unitScale
    fuelEnergyBasisAndUncertainty : Set
    oxygenAndHydrogenMeterCalibration : Set
    noStorageDepletionUnaccounted : Set
    noxAndParticulateMeasured : Set
    ambientAndDutyCycleControls : Set

open EngineRun public

-- An experimental comparison requires independently acquired observations.
-- Naming a test arm never constitutes performance or causal effect.
record PairedPerformanceStudy : Set₁ where
  field
    original : EngineRun
    poweredControl : EngineRun
    hydrogenControl : EngineRun
    oxygenControl : EngineRun
    complete : EngineRun
    originalArm : testArm original ≡ dieselBaseline
    poweredArm : testArm poweredControl ≡ poweredButNoGas
    hydrogenArm : testArm hydrogenControl ≡ externallyMeteredHydrogen
    oxygenArm : testArm oxygenControl ≡ oxygenOnly
    completeArm : testArm complete ≡ fullRetrofit
    identicalUsefulOutput : Set
    randomisationOrCrossover : Set
    independentInstrumentReceipts : Set
    residualBiasAndStatisticalUncertainty : Set

open PairedPerformanceStudy public

-- The interval savings theorem is a mathematical consumer of values admitted
-- by the study. The user must independently connect actual fuel/energy
-- readings to that study and its relevant source runs.
record AdmittedStudySavings : Set₁ where
  field
    study : PairedPerformanceStudy
    robustInputSaving : Interval.IntervalRunReceipt
    fuelAndElectricityDerivedFromStudy : Set
    loadEquivalencePaid : Set
    reproducibilityPaid : Set

open AdmittedStudySavings public

studyNetEnergyReduction :
  (s : AdmittedStudySavings) →
  Interval.IntervalRunReceipt.actualAssistedDiesel (robustInputSaving s)
    + Interval.IntervalRunReceipt.actualExternalElectricalInput
        (robustInputSaving s)
    < Interval.IntervalRunReceipt.actualBaselineDiesel
        (robustInputSaving s)
studyNetEnergyReduction s =
  Interval.actualInputReduction (robustInputSaving s)

-- Legal-claim or vendor claim evidence does not have the physical
-- instrument-measurement constructor. This is a classification guard,
-- not a test of whether any individual legal statement is correct.
claimStatusDoesNotProveMeasurement :
  Chemistry.patentDisclosed ≡ Chemistry.directlyMeasured → ⊥
claimStatusDoesNotProveMeasurement ()
