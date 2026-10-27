{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratorySensitivitySourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LABORATORY SENSITIVITY SOURCE ATLAS
--
-- These are benchmark/authority sources for instrument scale only.  None of
-- them prepares two systems with matched conventional stress-energy and a
-- deliberately different quantum-history / birthmark record.  Therefore they
-- are transfer-sensitivity references, not constraints on a history sector.
------------------------------------------------------------------------

record LaboratorySensitivitySource : Set where
  constructor laboratory-sensitivity-source
  field
    identifier : String
    title : String
    date : String
    sourceClass : String
    benchmarkReading : String

open LaboratorySensitivitySource public

milligramTorsion2026 : LaboratorySensitivitySource
milligramTorsion2026 =
  laboratory-sensitivity-source
    "doi:10.1038/s41467-026-78187-4"
    "Test of the gravitational interaction between milligram masses using a miniature torsion pendulum"
    "2026-10"
    "published experiment"
    "Two 7.6 mg silicon wafers; separations 0.654--1.554 mm; maximum quoted force uncertainty 50 aN at 2 sigma; Newtonian agreement."

latticeAtomInterferometer2024 : LaboratorySensitivitySource
latticeAtomInterferometer2024 =
  laboratory-sensitivity-source
    "doi:10.1038/s41586-024-07561-3"
    "Measuring gravitational attraction with a lattice atom interferometer"
    "2024"
    "published experiment"
    "Measured miniature-source acceleration 33.3 +/- 5.6_stat +/- 2.7_syst nm s^-2, consistent with Newtonian gravity."

quantumReadyOptomechanics2026 : LaboratorySensitivitySource
quantumReadyOptomechanics2026 =
  laboratory-sensitivity-source
    "arXiv:2607.18351"
    "Probing gravitational interaction between milligram optomechanical oscillators operating in the quantum regime"
    "2026-07-20"
    "ongoing experiment / sensitivity study"
    "23 mg physical gravity mass, 550 micrometre target separation, oscillating gravity-force amplitude 1.86--9.3 aN, thermal force ASD 4.5e-16 N/sqrt(Hz), unit-SNR full-gravity integration from minutes to about 15 h depending on drive."

currentExperimentsDidNotTestHistoryConditioning : Bool
currentExperimentsDidNotTestHistoryConditioning = true

transferSensitivitySourcesAreNotHistorySectorMeasurements : Bool
transferSensitivitySourcesAreNotHistorySectorMeasurements = true

publishedMilligramGravityDetectionExists : Bool
publishedMilligramGravityDetectionExists = true

quantumReadyOptomechanicalGravityMeasurementCompleted : Bool
quantumReadyOptomechanicalGravityMeasurementCompleted = false
