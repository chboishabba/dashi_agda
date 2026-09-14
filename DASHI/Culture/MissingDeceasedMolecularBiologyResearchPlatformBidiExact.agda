module DASHI.Culture.MissingDeceasedMolecularBiologyResearchPlatformBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R

bioSource : Source.AttributedSource
bioSource = Source.mkNoDOISource
  "DASHI source composite"
  "Molecular/chemical-biology research platform requirements"
  "composition of retained action-spectroscopy, signalling-assay and photopharmacology sources"
  "current formalisation"
  "DASHI in-repo source owners"
  (Source.namedSourceKind "formalisation composite")
  "Defines a benign laboratory object over separately attributed biological and spectroscopic science."
  Source.publicAttribution

bioAtlas : Source.AttributedSourceAtlas
bioAtlas = Source.mkSourceAtlas
  "molecular/biology research-platform atlas"
  "DASHI.Culture.MissingDeceasedMolecularBiologyResearchPlatformBidiExact"
  (bioSource ∷ [])
  "No medical efficacy, human use, historical programme or event-cause claim is created by object fit."

molecularDiagnosticsRequirement : R.RealObjectRequirement
molecularDiagnosticsRequirement = R.mkRequirement
  "molecular diagnostics"
  "identify and discriminate molecular species or conformational states with calibrated source-specific spectroscopy"
  "Maiwald action-spectroscopy lineage"
  (T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ [])
  "A spectroscopy method requires sample, tag, detector and calibration transfer before platform qualification."

cellAssayRequirement : R.RealObjectRequirement
cellAssayRequirement = R.mkRequirement
  "cell-signalling perturbation and assay"
  "apply controlled perturbations and measure source-specific pathway/readout changes with validation and target-deconvolution discipline"
  "Jason R. Thomas STING/ferritinophagy source lineage"
  (T.acquireValidationCorpus ∷ T.acquireCalibrationState ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ [])
  "Assay hits do not automatically establish direct mechanism or clinical relevance."

photochemicalControlRequirement : R.RealObjectRequirement
photochemicalControlRequirement = R.mkRequirement
  "light-controlled molecular intervention"
  "drive and observe source-specific photoswitch/probe state changes under calibrated wavelength, dose and kinetics"
  "Li Minyong photopharmacology/probe lineage"
  (T.acquireOperatingWindow ∷ T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ [])
  "Photochemical control in research systems does not establish therapeutic efficacy or human-use suitability."

dataGovernanceRequirement : R.RealObjectRequirement
dataGovernanceRequirement = R.mkRequirement
  "research-data governance"
  "maintain lifecycle, provenance, access and evidence controls around experimental data"
  "Liu Donghao DSMM governance lineage"
  (T.acquireIntegrationWorkflow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Governance maturity is not a cryptographic primitive or scientific-result validator."

molecularBiologyResearchPlatform : R.RealEngineeringObject
molecularBiologyResearchPlatform = R.real-engineering-object
  "molecular diagnostics and chemical-biology research platform"
  "benign laboratory research object"
  bioAtlas
  (molecularDiagnosticsRequirement ∷ cellAssayRequirement ∷ photochemicalControlRequirement ∷ dataGovernanceRequirement ∷ [])
  "integrate molecular identification, controlled biological perturbation, photochemical control and governed data capture"
  "Engineering/laboratory compatibility does not establish a common historical programme, medical efficacy or event cause."

maiwaldMolecularDiagnosticsFit : R.ScientistObjectFit
maiwaldMolecularDiagnosticsFit = R.mkFit
  "Frank W. Maiwald"
  "DASHI Maiwald action-spectroscopy owners"
  "cryogenic tagged-ion vibrational/action spectroscopy"
  molecularDiagnosticsRequirement R.directSourceFit
  "DOI 10.1021/acs.jpca.4c03552"
  "Direct fit to calibrated molecular discrimination."
  "recover raw intensities, calibration, dissociation-time arrays and platform sample interface"
  false
  "Direct science fit does not establish platform participation."

jasonThomasChemicalBiologyFit : R.ScientistObjectFit
jasonThomasChemicalBiologyFit = R.mkFit
  "Jason R. Thomas"
  "DASHI Jason Thomas signalling/ferritinophagy owners"
  "STING-pathway and ferritinophagy perturbation/assay science"
  cellAssayRequirement R.directSourceFit
  "retained ACS Chemical Biology and signalling/ferritinophagy source surfaces"
  "Direct fit to source-specific cell-signalling assay and target-validation workflows."
  "recover supporting-information matrices, dose-response arrays and target-validation chain"
  false
  "Assay relevance does not establish a common programme or case cause."

liMinyongPhotopharmacologyFit : R.ScientistObjectFit
liMinyongPhotopharmacologyFit = R.mkFit
  "Li Minyong"
  "DASHI.Biology.LiMinyongPhotopharmacologyBidiExact"
  "photoswitch/probe molecular control and readout"
  photochemicalControlRequirement R.directSourceFit
  "photopharmacology review and exact probe/patent lineage retained in repo"
  "Direct fit to light-controlled molecular research and optical readout."
  "recover one exact molecule/probe wavelength-state-binding-readout finite replay and kinetics"
  false
  "Research-platform fit does not establish therapeutic efficacy or historical integration."

liuDataGovernanceFit : R.ScientistObjectFit
liuDataGovernanceFit = R.mkFit
  "Liu Donghao"
  "DASHI.ComputerScience.LiuDonghaoDSMMBidiExact"
  "data-security maturity and lifecycle governance"
  dataGovernanceRequirement R.methodTransfer
  "retained DSMM/data-security governance sources"
  "Method transfer can structure research-data lifecycle controls without becoming a scientific mechanism."
  "recover exact source assessment rubric and platform-specific governance implementation"
  false
  "Governance fit does not establish protected-data access or programme membership."

molecularBiologyFitPaysHistoricalProgramme : Bool
molecularBiologyFitPaysHistoricalProgramme = false
