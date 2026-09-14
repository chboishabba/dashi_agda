module DASHI.Culture.MissingDeceasedHighEnergyExperimentalFacilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R

facilitySource : Source.AttributedSource
facilitySource = Source.mkNoDOISource
  "DASHI source composite"
  "High-energy experimental and diagnostic facility requirements"
  "composition of DARHT/Scorpius, controls, materials, spectroscopy and precision-test source surfaces"
  "current formalisation"
  "DASHI in-repo source owners"
  (Source.namedSourceKind "formalisation composite")
  "Defines a benign experimental-facility consumer surface; not a historical common programme."
  Source.publicAttribution

highEnergyAtlas : Source.AttributedSourceAtlas
highEnergyAtlas = Source.mkSourceAtlas
  "high-energy experimental facility atlas"
  "DASHI.Culture.MissingDeceasedHighEnergyExperimentalFacilityBidiExact"
  (facilitySource ∷ [])
  "Capability fit remains separate from programme identity, possession, targeting and event cause."

radiographyRequirement : R.RealObjectRequirement
radiographyRequirement = R.mkRequirement
  "high-energy radiography / accelerator diagnostics"
  "generate, control and diagnose high-energy experimental pulses with source-specific timing and instrumentation"
  "LANL DARHT/Scorpius engineering carrier retained for Anthony Chavez"
  (T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Identity weld and subsystem-specific implementation remain prerequisites."

precisionForceRequirement : R.RealObjectRequirement
precisionForceRequirement = R.mkRequirement
  "precision anomalous-force discrimination"
  "test force/gravity claims with controls, calibration, null channels and explicit uncertainty"
  "Ning Li YBCO experimental lineage plus Amy mechanism-discrimination programme surface"
  (T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ [])
  "Null-test capability does not imply a positive exotic-force mechanism."

materialsRequirement : R.RealObjectRequirement
materialsRequirement = R.mkRequirement
  "extreme-environment materials and structures"
  "maintain structural/material integrity under experiment-specific thermal, mechanical, radiation or oxidising loads"
  "Reza/Zhou/Fang retained material and mechanics owners"
  (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Material science transfers only after facility-specific qualification."

diagnosticsRequirement : R.RealObjectRequirement
diagnosticsRequirement = R.mkRequirement
  "molecular and state diagnostics"
  "identify molecular/chemical species or state changes using calibrated spectroscopy and bounded inference"
  "Maiwald action-spectroscopy owner"
  (T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ [])
  "Spectroscopy method transfer requires facility-specific sample, detector and calibration state."

highEnergyExperimentalFacility : R.RealEngineeringObject
highEnergyExperimentalFacility = R.real-engineering-object
  "high-energy experimental / diagnostic research facility"
  "benign laboratory and test-infrastructure object"
  highEnergyAtlas
  (radiographyRequirement ∷ precisionForceRequirement ∷ materialsRequirement ∷ diagnosticsRequirement ∷ [])
  "study controlled high-energy experiments, diagnostics, materials response and precision null tests"
  "A multi-capability facility model does not establish one historical programme or operational targeting."

chavezRadiographyFit : R.ScientistObjectFit
chavezRadiographyFit = R.mkFit
  "Anthony Chavez"
  "LANL DARHT/Scorpius engineering carrier"
  "accelerator/radiographic engineering"
  radiographyRequirement R.directSourceFit
  "LANL engineering profile retained in investigation owners"
  "Direct source fit to high-energy radiography engineering, but the missing-person identity weld remains separately gated."
  "first pay same-person identity weld; then recover exact Scorpius/DARHT subsystem task identifiers"
  false
  "Science fit cannot cross an unpaid identity seam."

ningPrecisionForceFit : R.ScientistObjectFit
ningPrecisionForceFit = R.mkFit
  "Ning Li"
  "DASHI superconducting-gravity/YBCO experimental owners"
  "static and rotating superconducting-gravity null-test lineage"
  precisionForceRequirement R.directSourceFit
  "Physica C 1997 and NASA rotating-field manifestations"
  "Direct fit to precision anomalous-force testing, with published negative/null constraints retained."
  "recover later apparatus geometry, calibration/control state and Army SOW/closeout"
  false
  "Precision testing does not establish a positive propulsion mechanism or historical integrated facility."

maiwaldDiagnosticsFit : R.ScientistObjectFit
maiwaldDiagnosticsFit = R.mkFit
  "Frank W. Maiwald"
  "DASHI Maiwald action-spectroscopy owners"
  "cryogenic tagged-ion molecular diagnostics"
  diagnosticsRequirement R.methodTransfer
  "DOI 10.1021/acs.jpca.4c03552"
  "The calibrated spectroscopy method can transfer to an appropriate laboratory diagnostic subsystem."
  "recover raw spectra, calibration and sample-specific interface"
  false
  "Method transfer does not establish facility participation."

highEnergyFitPaysHistoricalFacility : Bool
highEnergyFitPaysHistoricalFacility = false
