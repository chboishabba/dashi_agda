module DASHI.Core.CalibratedExperimentInferenceExact where

open import DASHI.Core.Prelude
import DASHI.Core.PredictionEnvelopeExact as Envelope

------------------------------------------------------------------------
-- Stage-6 calibrated experiment architecture.
--
-- The purpose of this module is not to rebuild the Lean analytic library in
-- Agda.  It fixes the same semantic boundaries on the Agda side: deterministic
-- admissibility, posterior support, coverage procedures, certified
-- sensitivities, dynamical traces and repair status remain different objects.
------------------------------------------------------------------------

data RegionSemantics : Set where
  deterministicEnvelope : RegionSemantics
  posteriorSupport : RegionSemantics
  confidenceProcedure : RegionSemantics

deterministicNotPosterior :
  ¬ (deterministicEnvelope ≡ posteriorSupport)
deterministicNotPosterior ()

posteriorNotConfidence :
  ¬ (posteriorSupport ≡ confidenceProcedure)
posteriorNotConfidence ()

deterministicNotConfidence :
  ¬ (deterministicEnvelope ≡ confidenceProcedure)
deterministicNotConfidence ()

record ExperimentFamily : Set₁ where
  constructor experimentFamily
  field
    State : Set
    Parameter : Set
    Control : Set
    Observation : Set
    Prediction : Set
    Risk : Set
    Evidence : Set

    stateAt : Parameter → Control → State
    observe : State → Observation
    predict : State → Prediction
    risk : State → Risk
    compatible : Evidence → Parameter → Set

open ExperimentFamily public

record DataRefinement (family : ExperimentFamily) : Set₁ where
  constructor dataRefinement
  field
    refinedEvidence : Evidence family
    previousEvidence : Evidence family
    refinement :
      ∀ parameter →
      compatible family refinedEvidence parameter →
      compatible family previousEvidence parameter

open DataRefinement public

refinementPreservesAdmissibility :
  ∀ {family : ExperimentFamily}
    (selection : DataRefinement family)
    (parameter : Parameter family) →
  compatible family (refinedEvidence selection) parameter →
  compatible family (previousEvidence selection) parameter
refinementPreservesAdmissibility selection parameter =
  refinement selection parameter

------------------------------------------------------------------------
-- Weighted inference is allowed to sit inside deterministic admissibility, but
-- a support predicate carries no weights by itself.
------------------------------------------------------------------------

record PosteriorSupportInside
    (family : ExperimentFamily)
    (evidence : Evidence family) : Set₁ where
  constructor posteriorSupportInside
  field
    Supported : Parameter family → Set
    supportIsAdmissible :
      ∀ parameter →
      Supported parameter → compatible family evidence parameter

open PosteriorSupportInside public

posteriorSupportIsInsideDeterministicRegion :
  ∀ {family : ExperimentFamily}
    {evidence : Evidence family}
    (posterior : PosteriorSupportInside family evidence)
    (parameter : Parameter family) →
  Supported posterior parameter →
  compatible family evidence parameter
posteriorSupportIsInsideDeterministicRegion posterior parameter =
  supportIsAdmissible posterior parameter

------------------------------------------------------------------------
-- Coverage and posterior mass remain independent semantics.  These records
-- intentionally do not coerce into one another.
------------------------------------------------------------------------

record CoverageProcedure
    (Parameter Observation : Set) : Set₁ where
  constructor coverageProcedure
  field
    Contains : Observation → Parameter → Set
    CoverageWitness : Set

record CredibleProcedure
    (Parameter Observation : Set) : Set₁ where
  constructor credibleProcedure
  field
    Contains : Observation → Parameter → Set
    PosteriorMassWitness : Set

------------------------------------------------------------------------
-- Sensitivity certification keeps declared metadata separate from a proof that
-- the metadata is actually the derivative/sensitivity object required by the
-- law.  The theorem below is deliberately just projection of the certificate:
-- the certificate, not the declaration, carries authority.
------------------------------------------------------------------------

record CertifiedSensitivity
    (Input Output Sensitivity : Set)
    (law : Input → Output)
    (declared : Input → Sensitivity) : Set₁ where
  constructor certifiedSensitivity
  field
    TrueSensitivity : Input → Sensitivity
    declaredIsTrue : ∀ input → declared input ≡ TrueSensitivity input

open CertifiedSensitivity public

certifiedSensitivityUsesProvedRow :
  ∀ {Input Output Sensitivity : Set}
    {law : Input → Output}
    {declared : Input → Sensitivity}
    (certificate : CertifiedSensitivity Input Output Sensitivity law declared)
    (input : Input) →
  declared input ≡ TrueSensitivity certificate input
certifiedSensitivityUsesProvedRow certificate input =
  declaredIsTrue certificate input

------------------------------------------------------------------------
-- Dynamical sensitivity is similarly evidence-bearing: a variational law is a
-- hypothesis/certificate over a trajectory, not something obtained from the
-- mere existence of a trace.
------------------------------------------------------------------------

record TrajectorySensitivity
    (Time State Parameter Sensitivity : Set)
    (trajectory : Parameter → Time → State) : Set₁ where
  constructor trajectorySensitivity
  field
    sensitivity : Parameter → Time → Sensitivity
    variationalLaw : Set
    initialSensitivityLaw : Set

------------------------------------------------------------------------
-- Repair classes are typed before any search procedure is admitted.
------------------------------------------------------------------------

data RepairClass : Set where
  parameterExtension : RepairClass
  latentStateExtension : RepairClass
  interactionExtension : RepairClass
  dynamicsRevision : RepairClass
  measurementModelRevision : RepairClass
  sourceAssumptionRevision : RepairClass

record RepairProposal : Set₁ where
  constructor repairProposal
  field
    repairClass : RepairClass
    fitRestored : Set
    refutableByNewEvidence : Set
    independentSupport : Set

------------------------------------------------------------------------
-- Stage-6 boundary: fit, coverage, posterior mass and support are deliberately
-- non-identical claims.
------------------------------------------------------------------------

record CalibratedExperimentBoundary : Set where
  constructor calibratedExperimentBoundary
  field
    deterministicEnvelopeEqualsPosteriorSupport : Bool
    deterministicEnvelopeEqualsPosteriorSupportIsFalse :
      deterministicEnvelopeEqualsPosteriorSupport ≡ false

    posteriorMassEqualsFrequentistCoverage : Bool
    posteriorMassEqualsFrequentistCoverageIsFalse :
      posteriorMassEqualsFrequentistCoverage ≡ false

    declaredSensitivityIsAutomaticallyCertified : Bool
    declaredSensitivityIsAutomaticallyCertifiedIsFalse :
      declaredSensitivityIsAutomaticallyCertified ≡ false

    restoredFitAutomaticallySuppliesIndependentSupport : Bool
    restoredFitAutomaticallySuppliesIndependentSupportIsFalse :
      restoredFitAutomaticallySuppliesIndependentSupport ≡ false

canonicalCalibratedExperimentBoundary : CalibratedExperimentBoundary
canonicalCalibratedExperimentBoundary =
  calibratedExperimentBoundary
    false refl
    false refl
    false refl
    false refl
