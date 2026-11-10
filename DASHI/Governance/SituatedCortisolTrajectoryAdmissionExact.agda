module DASHI.Governance.SituatedCortisolTrajectoryAdmissionExact where

-- Individual-specific, time-indexed HPA response model ADMISSION.
-- DASHI-original formal interface, reusing prior embodied physiology.
-- Sources motivate which factors to measure, not a unique model parameter:
-- Dickerson & Kemeny (2004), DOI 10.1037/0033-2909.130.3.355
-- Khoury et al (2019), DOI 10.1016/j.psyneuen.2019.01.009
-- Crenshaw (1989, 1991): relational/intersectional context, not
-- cortisol data and not an author of the HPA equations.
-- Quantitative predictions are NOT produced without real person-time
-- observations, an assay model, consent/access, and validation.
open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.StressPhysiologyCascadeExact as Cascade
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied

data ExposureDimension : Set where
  socialEvaluativeThreat uncontrollability
  accessToSupport resourceConstraint
  institutionalDiscretion : ExposureDimension

data PhysiologyDimension : Set where
  circadianPhase priorHPARegime sleepContext
  medicationContext assayMatrix
  acuteAutonomicState : PhysiologyDimension

-- Ternary axes are qualitative source/observer states, not cortisol
-- concentrations. We do not derive physiology from race/gender labels.
data QualitativeLevel : Set where
  lower middle higher unknown : QualitativeLevel

record SituatedTimeSlice : Set where
  constructor situated-time-slice
  field
    exposure : ExposureDimension → QualitativeLevel
    bodyContext : PhysiologyDimension → QualitativeLevel

open SituatedTimeSlice public

data SampleMatrix : Set where
  saliva blood hair otherMatrix : SampleMatrix

record PersonTimeObservation
  (Person Time : Set)
  (person : Person)
  (time : Time) : Set₁ where
  field
    observedExposures : SituatedTimeSlice
    sourceRecordForExposure : Set
    sourceRecordForBodyContext : Set
    sourceMatchedTime : Set
    samplingMatrix : SampleMatrix
    samplingTimeVerified : Set
    observedCortisol : Nat
    cortisolAssayUnit : String
    hormoneAssayValidated : Set
    collectionConsentAndAccess : Set

-- The Nat value is a placeholder for a measured encoded quantity.
-- Unit, matrix and calibration are NOT supplied by the type itself.
-- Real concentration is only interpretable with independently paid
-- external evidence (assay and sampling receipts).

record CalibratedPersonalDynamics
  (Person Time LatentState : Set) : Set₁ where
  field
    chosenPerson : Person
    latentAt : Time → LatentState
    individualizedTransition :
      Person → Time → LatentState → SituatedTimeSlice → LatentState
    cortisolReadout : Person → Time → LatentState → Nat
    validatedInitialCondition : Set
    parameterIdentificationEvidence : Set
    temporalSampleAlignmentEvidence : Set
    withinPersonCalibrationEvidence : Set
    counterfactualScopeReviewed : Set
    outOfSamplePredictiveValidation : Set

open CalibratedPersonalDynamics public

-- Projection of a person-indexed latent state into a cortisol prediction.
-- This is conditional on the caller-supplied calibrated dynamics and does
-- not assert that the selected predictions are clinically accurate.
predictCortisol :
  ∀ {Person Time LatentState : Set}
  (model : CalibratedPersonalDynamics Person Time LatentState) →
  Time → Nat
predictCortisol model t =
  cortisolReadout model (chosenPerson model) t (latentAt model t)

-- No census aggregate can inhabit person-time assay validation merely
-- by matching a cohort average.
record PersonSpecificAdmission
  {Person Time LatentState : Set}
  (model : CalibratedPersonalDynamics Person Time LatentState)
  (time : Time) : Set where
  constructor person-specific-admission
  field
    initialStatePaid : validatedInitialCondition model
    parametersPaid : parameterIdentificationEvidence model
    timeAlignmentPaid : temporalSampleAlignmentEvidence model
    individualFitPaid : withinPersonCalibrationEvidence model
    externalValidationPaid : outOfSamplePredictiveValidation model

open PersonSpecificAdmission public

admissionRequiresIndividualCalibration :
  ∀ {Person Time LatentState : Set}
    {model : CalibratedPersonalDynamics Person Time LatentState}
    {t : Time} →
  PersonSpecificAdmission model t →
  withinPersonCalibrationEvidence model
admissionRequiresIndividualCalibration = individualFitPaid

admissionRequiresExternalValidation :
  ∀ {Person Time LatentState : Set}
    {model : CalibratedPersonalDynamics Person Time LatentState}
    {t : Time} →
  PersonSpecificAdmission model t →
  outOfSamplePredictiveValidation model
admissionRequiresExternalValidation = externalValidationPaid

-- Finite interaction: the same coarsely scored external 'load' may have
-- different qualitative candidate appraisal contexts.
-- This is a structural witness, not a universal cortisol response law.
data IndividualContext : Set where
  highSupport lowSupport : IndividualContext

data CandidateAppraisal : Set where
  manageable highThreat : CandidateAppraisal

aggregateLoad : IndividualContext → QualitativeLevel
aggregateLoad _ = higher

candidateAppraisal : IndividualContext → CandidateAppraisal
candidateAppraisal highSupport = manageable
candidateAppraisal lowSupport = highThreat

sameAggregateDifferentSituatedAppraisal :
  NF.NonFactorabilityWitness aggregateLoad candidateAppraisal
sameAggregateDifferentSituatedAppraisal =
  NF.nonFactorabilityWitness highSupport lowSupport refl (λ ())

aggregateLoadDoesNotFixAppraisal :
  NF.FactorsThrough aggregateLoad candidateAppraisal → ⊥
aggregateLoadDoesNotFixAppraisal =
  NF.witnessRulesOutEveryFlatFactorisation
    sameAggregateDifferentSituatedAppraisal

-- Bridge to existing original physiology *timescale distinctions*.
fastRouteNotEndocrineTime :
  Cascade.mediatorTimescale Cascade.norepinephrine
    ≡ Cascade.mediatorTimescale Cascade.cortisol → ⊥
fastRouteNotEndocrineTime =
  Cascade.norepinephrineAndCortisolTimescalesDiffer

-- Stronger, calibrated temporal prediction and physiological causality
-- remain open until independently supplied empirical receipts exist.
