module DASHI.Biology.PMDDHistamineInterventionIdentificationBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.PMDDHistamineAmplificationExact as PMDD
import DASHI.Biology.PMDDHistamineMolecularTargetInstantiationExact as Molecular
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal

------------------------------------------------------------------------
-- PMDD / HISTAMINE INTERVENTION IDENTIFICATION BOUNDARY
--
-- A reproducible H1/H2 response can be evidence that the perturbed channels
-- matter to an observed phenotype.  It does not uniquely identify:
--   * the upstream source of histamine,
--   * the compartment in which the relevant action occurred,
--   * whether histamine is primary or amplifying,
--   * a biological subtype,
--   * or a universal PMDD mechanism.
--
-- This module makes that distinction proof-relevant by consuming the repo's
-- existing observation-vs-causal-realisation boundary.
------------------------------------------------------------------------

causalBoundary :
  Causal.FibreSufficiencyCausalInterventionBoundary
causalBoundary =
  Causal.canonicalFibreSufficiencyCausalInterventionBoundary

parentCandidate :
  PMDD.HistamineAmplifiedPMDDCandidate
parentCandidate =
  PMDD.canonicalHistamineAmplifiedPMDDCandidate

molecularCandidate :
  Molecular.MolecularlyInstantiatedPMDDHistamineCandidate
molecularCandidate =
  Molecular.canonicalMolecularlyInstantiatedPMDDHistamineCandidate

------------------------------------------------------------------------
-- Factorial perturbation surface.
------------------------------------------------------------------------

data H1Assignment : Set where
  h1Open : H1Assignment
  h1Blocked : H1Assignment

data H2Assignment : Set where
  h2Open : H2Assignment
  h2Blocked : H2Assignment

record HistaminePerturbationArm : Set where
  constructor histaminePerturbationArm
  field
    h1 : H1Assignment
    h2 : H2Assignment

open HistaminePerturbationArm public

baselineArm : HistaminePerturbationArm
baselineArm =
  histaminePerturbationArm h1Open h2Open

h1OnlyArm : HistaminePerturbationArm
h1OnlyArm =
  histaminePerturbationArm h1Blocked h2Open

h2OnlyArm : HistaminePerturbationArm
h2OnlyArm =
  histaminePerturbationArm h1Open h2Blocked

dualBlockadeArm : HistaminePerturbationArm
dualBlockadeArm =
  histaminePerturbationArm h1Blocked h2Blocked

canonicalFactorialArms : List HistaminePerturbationArm
canonicalFactorialArms =
  baselineArm
  ∷ h1OnlyArm
  ∷ h2OnlyArm
  ∷ dualBlockadeArm
  ∷ []

data CycleWindow : Set where
  follicularReferenceWindow : CycleWindow
  lutealSymptomWindow : CycleWindow
  perimenstrualTransitionWindow : CycleWindow

record ProtocolCoordinate : Set where
  constructor protocolCoordinate
  field
    arm : HistaminePerturbationArm
    cycleWindow : CycleWindow
    participantReference : String
    exposureReference : String
    timingReference : String
    symptomReadoutReference : String
    mediatorReadoutReference : String
    steroidReadoutReference : String

open ProtocolCoordinate public

------------------------------------------------------------------------
-- Observation status remains distinct from causal interpretation.
------------------------------------------------------------------------

data ResponseObservation : Set where
  noMaterialSymptomChange : ResponseObservation
  symptomReductionObserved : ResponseObservation
  symptomIncreaseObserved : ResponseObservation

data CausalInterpretation : Set where
  h1DominantContribution : CausalInterpretation
  h2DominantContribution : CausalInterpretation
  jointHistamineChannelContribution : CausalInterpretation
  peripheralHistamineAmplifier : CausalInterpretation
  centralHistamineAmplifier : CausalInterpretation
  nonHistamineMediatedDrugEffect : CausalInterpretation
  mixedOrUnresolvedMechanism : CausalInterpretation

record PerturbationObservation : Set where
  constructor perturbationObservation
  field
    protocol : ProtocolCoordinate
    response : ResponseObservation
    interpretation : CausalInterpretation

    observationRecorded : Bool
    observationRecordedIsTrue :
      observationRecorded ≡ true

    causalInterpretationIdentified : Bool
    causalInterpretationIdentifiedIsFalse :
      causalInterpretationIdentified ≡ false

open PerturbationObservation public

dualResponseCandidateA : PerturbationObservation
dualResponseCandidateA =
  perturbationObservation
    (protocolCoordinate
      dualBlockadeArm
      lutealSymptomWindow
      "same participant"
      "pre-specified H1 plus H2 perturbation"
      "cycle-locked timing"
      "prospective symptom scale"
      "histamine/mast-cell readout unresolved"
      "steroid/neurosteroid readout unresolved")
    symptomReductionObserved
    jointHistamineChannelContribution
    true refl
    false refl

dualResponseCandidateB : PerturbationObservation
dualResponseCandidateB =
  perturbationObservation
    (protocolCoordinate
      dualBlockadeArm
      lutealSymptomWindow
      "same participant"
      "pre-specified H1 plus H2 perturbation"
      "cycle-locked timing"
      "prospective symptom scale"
      "histamine/mast-cell readout unresolved"
      "steroid/neurosteroid readout unresolved")
    symptomReductionObserved
    nonHistamineMediatedDrugEffect
    true refl
    false refl

sameObservedResponseDifferentCausalReading :
  response dualResponseCandidateA
  ≡
  response dualResponseCandidateB
sameObservedResponseDifferentCausalReading =
  refl

------------------------------------------------------------------------
-- Identification gates.
------------------------------------------------------------------------

record HistamineInterventionIdentificationBoundary : Set where
  constructor histamineInterventionIdentificationBoundary
  field
    fourArmFactorialSurfaceAvailable : Bool
    fourArmFactorialSurfaceAvailableIsTrue :
      fourArmFactorialSurfaceAvailable ≡ true

    cycleWindowIndexed : Bool
    cycleWindowIndexedIsTrue :
      cycleWindowIndexed ≡ true

    symptomResponseCanUpdateHypothesis : Bool
    symptomResponseCanUpdateHypothesisIsTrue :
      symptomResponseCanUpdateHypothesis ≡ true

    responseAloneIdentifiesMechanism : Bool
    responseAloneIdentifiesMechanismIsFalse :
      responseAloneIdentifiesMechanism ≡ false

    responseAloneIdentifiesHistamineSource : Bool
    responseAloneIdentifiesHistamineSourceIsFalse :
      responseAloneIdentifiesHistamineSource ≡ false

    responseAloneIdentifiesCompartment : Bool
    responseAloneIdentifiesCompartmentIsFalse :
      responseAloneIdentifiesCompartment ≡ false

    responseAloneEstablishesBiologicalSubtype : Bool
    responseAloneEstablishesBiologicalSubtypeIsFalse :
      responseAloneEstablishesBiologicalSubtype ≡ false

    responseAloneEstablishesTreatmentEfficacy : Bool
    responseAloneEstablishesTreatmentEfficacyIsFalse :
      responseAloneEstablishesTreatmentEfficacy ≡ false

    h1MainEffectRequiresComparison : Bool
    h1MainEffectRequiresComparisonIsTrue :
      h1MainEffectRequiresComparison ≡ true

    h2MainEffectRequiresComparison : Bool
    h2MainEffectRequiresComparisonIsTrue :
      h2MainEffectRequiresComparison ≡ true

    h1h2InteractionRequiresComparison : Bool
    h1h2InteractionRequiresComparisonIsTrue :
      h1h2InteractionRequiresComparison ≡ true

open HistamineInterventionIdentificationBoundary public

canonicalHistamineInterventionIdentificationBoundary :
  HistamineInterventionIdentificationBoundary
canonicalHistamineInterventionIdentificationBoundary =
  histamineInterventionIdentificationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Minimal causal design obligations.
------------------------------------------------------------------------

record FactorialIdentificationFrontier : Set where
  constructor factorialIdentificationFrontier
  field
    h1Contrast : String
    h2Contrast : String
    interactionContrast : String
    cycleLock : String
    carryoverControl : String
    mediatorMeasurement : String
    steroidMeasurement : String
    replicationRule : String

canonicalFactorialIdentificationFrontier :
  FactorialIdentificationFrontier
canonicalFactorialIdentificationFrontier =
  factorialIdentificationFrontier
    "compare H1-blocked versus H1-open conditions while preserving H2 assignment and cycle window"
    "compare H2-blocked versus H2-open conditions while preserving H1 assignment and cycle window"
    "compare observed dual-blockade response against the response expected from separate H1 and H2 effects under a declared interaction model"
    "repeat comparable perturbation arms in matched menstrual-cycle windows"
    "declare washout/carryover handling rather than treating adjacent cycles as exchangeable by default"
    "collect a protocol-indexed histamine/mast-cell mediator coordinate if mechanism identification is claimed"
    "collect ovarian-steroid/neurosteroid coordinates if interaction with the primary PMDD lane is claimed"
    "replicate the within-person pattern and then across participants before introducing a subtype label"

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data SymptomResponseDeterminesMechanism : Set where
data DualBlockadeDeterminesHistamineSource : Set where
data SingleParticipantResponseDefinesSubtype : Set where
data FactorialDesignByItselfCreatesClinicalEfficacy : Set where

symptomResponseDoesNotDetermineMechanism :
  SymptomResponseDeterminesMechanism → ⊥
symptomResponseDoesNotDetermineMechanism ()

dualBlockadeDoesNotDetermineHistamineSource :
  DualBlockadeDeterminesHistamineSource → ⊥
dualBlockadeDoesNotDetermineHistamineSource ()

singleParticipantResponseDoesNotDefineSubtype :
  SingleParticipantResponseDefinesSubtype → ⊥
singleParticipantResponseDoesNotDefineSubtype ()

factorialDesignDoesNotCreateClinicalEfficacy :
  FactorialDesignByItselfCreatesClinicalEfficacy → ⊥
factorialDesignDoesNotCreateClinicalEfficacy ()
