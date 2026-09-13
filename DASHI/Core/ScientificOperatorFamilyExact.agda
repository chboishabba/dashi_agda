module DASHI.Core.ScientificOperatorFamilyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SHARED SCIENTIFIC OPERATOR FAMILIES
--
-- These are reusable scientific operator shapes, not claims that two domains
-- have identical equations, empirical mechanisms, programmes or provenance.
------------------------------------------------------------------------

data ScientificOperatorFamily : Set where
  weakSignalInverseInference
  resilientSensingControlVerification
  materialsProcessStructureProperty
  molecularSpectroscopyChemicalBiology
  fieldPlasmaPrecisionForceDiscrimination
  classificationEvidenceGovernance : ScientificOperatorFamily

record ScientificOperatorShape : Set where
  constructor scientific-operator-shape
  field
    family : ScientificOperatorFamily
    inputRole : String
    transformRole : String
    outputRole : String
    reverseScientificObligation : String

open ScientificOperatorShape public

weakSignalShape : ScientificOperatorShape
weakSignalShape = scientific-operator-shape
  weakSignalInverseInference
  "noisy/sparse observation field plus an explicit observation model"
  "filter, decompose, match, phase-fold or otherwise extract a structured candidate"
  "candidate latent structure with uncertainty / non-unique inverse fibre"
  "acquire the measurement/model coordinates needed to shrink the compatible latent-state fibre"

resilientControlShape : ScientificOperatorShape
resilientControlShape = scientific-operator-shape
  resilientSensingControlVerification
  "environment/state plus sensors, models and admissible control/verification coordinates"
  "sense, verify or estimate state, then route robust/fault-aware control action"
  "bounded response, placement, verification or tracking result with failure residuals"
  "acquire qualification, dynamics, failure-family, coverage or response evidence needed by the consumer"

materialsProcessShape : ScientificOperatorShape
materialsProcessShape = scientific-operator-shape
  materialsProcessStructureProperty
  "composition, geometry and/or processing coordinates"
  "map process/design variables through latent material/structural state to measured properties"
  "finite property vector or admissible design/process frontier"
  "acquire process-state, microstructure, uncertainty and multi-sample property data for reverse design"

molecularMeasurementShape : ScientificOperatorShape
molecularMeasurementShape = scientific-operator-shape
  molecularSpectroscopyChemicalBiology
  "molecular state plus excitation, perturbation or probe coordinates"
  "drive state change or assay perturbation and measure optical/fragment/biochemical response"
  "molecular/target/configuration inference with measurement residuals"
  "acquire calibration, raw response and direct-target/configuration validation"

fieldComparatorShape : ScientificOperatorShape
fieldComparatorShape = scientific-operator-shape
  fieldPlasmaPrecisionForceDiscrimination
  "field/material/apparatus state plus a governing model or comparator"
  "evolve the model or execute a controlled/null comparison across apparatus regimes"
  "observable, residual or discrimination result"
  "acquire controls, calibration and regime-identical comparator evidence before mechanism promotion"

classificationEvidenceShape : ScientificOperatorShape
classificationEvidenceShape = scientific-operator-shape
  classificationEvidenceGovernance
  "uncertain/noisy observations, labels, controls or evidence items"
  "classify, verify or assess against an attributable decision/evidence rule"
  "evidence-bearing class, maturity, verification or decision state"
  "acquire exact rule/scoring semantics, source examples and error/coverage evidence"

record OperatorFactorisation : Set where
  constructor operator-factorisation
  field
    person : String
    domainOwner : String
    operatorShape : ScientificOperatorShape
    scienceSurface : String
    boundedReading : String

open OperatorFactorisation public

familySharingImpliesSameEquations : Bool
familySharingImpliesSameEquations = false

familySharingImpliesSameMechanism : Bool
familySharingImpliesSameMechanism = false

familySharingImpliesSameProgramme : Bool
familySharingImpliesSameProgramme = false

familySharingImpliesCollaboration : Bool
familySharingImpliesCollaboration = false

familySharingImpliesCommonCause : Bool
familySharingImpliesCommonCause = false

operatorFactorisationCanSupportReuse : Bool
operatorFactorisationCanSupportReuse = true
