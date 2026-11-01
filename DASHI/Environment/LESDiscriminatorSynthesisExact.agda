module DASHI.Environment.LESDiscriminatorSynthesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- LES discriminator-synthesis adapter.
--
-- Uses one DomainMechanismSocket as the fine state/action/observation owner.
-- Candidate measurements may be cheaper than increasing model fidelity, or a
-- fidelity increase may itself be the cheapest obstruction-removing move.
------------------------------------------------------------------------

record LESMeasurementLibrary
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesMeasurementLibrary
  field
    ExistingCode : Set
    existingObserver : Basis.State mechanism → ExistingCode
    DeclaredMeasurement :
      Synthesis.ExperimentBundle (Basis.State mechanism) → Set
    libraryReference : String
    calibrationAuthorityReference : String

open LESMeasurementLibrary public

record LESMinimalDiscriminator
    {mechanism : Basis.DomainMechanismSocket}
    (library : LESMeasurementLibrary mechanism) : Set₁ where
  constructor lesMinimalDiscriminator
  field
    synthesis :
      Synthesis.MinimalDiscriminator
        (existingObserver library)
        (DeclaredMeasurement library)
    consumerReference : String
    siteSpeciesSeasonReference : String
    nuisanceReference : String
    validationReference : String

open LESMinimalDiscriminator public

------------------------------------------------------------------------
-- Evidence-aware actionability bridge.  The current obstruction can be an
-- unresolved robust-control conflict over the compatible-state fibre.
------------------------------------------------------------------------

record LESEvidenceActionabilitySynthesis
    {mechanism : Basis.DomainMechanismSocket}
    {Evidence : Set}
    (library : LESMeasurementLibrary mechanism) : Set₁ where
  constructor lesEvidenceActionabilitySynthesis
  field
    compatible : Envelope.Compatible Evidence (Basis.State mechanism)
    evidence : Evidence
    actionabilityProblem : Choice.ActionabilityProblem
    selectedDiscriminator : LESMinimalDiscriminator library
    resolvesActionability :
      Choice.Resolves actionabilityProblem
        (Synthesis.bundleInformationMove
          (Synthesis.selected (synthesis selectedDiscriminator)))
        (Choice.currentObstruction actionabilityProblem)
    evidenceReference : String
    robustControlReference : String
    authorityReference : String

open LESEvidenceActionabilitySynthesis public

record LESDiscriminatorSynthesisBoundary : Set where
  constructor lesDiscriminatorSynthesisBoundary
  field
    anotherSensorIsAlwaysBetterThanFidelityEscalation : Bool
    anotherSensorIsAlwaysBetterThanFidelityEscalationIsFalse :
      anotherSensorIsAlwaysBetterThanFidelityEscalation ≡ false

    fidelityEscalationIsAlwaysBetterThanAnotherMeasurement : Bool
    fidelityEscalationIsAlwaysBetterThanAnotherMeasurementIsFalse :
      fidelityEscalationIsAlwaysBetterThanAnotherMeasurement ≡ false

    selectedMeasurementStillNeedsCalibrationAndValidation : Bool
    selectedMeasurementStillNeedsCalibrationAndValidationIsTrue :
      selectedMeasurementStillNeedsCalibrationAndValidation ≡ true

    resolvingActionabilityAutomaticallyAuthorisesIntervention : Bool
    resolvingActionabilityAutomaticallyAuthorisesInterventionIsFalse :
      resolvingActionabilityAutomaticallyAuthorisesIntervention ≡ false

canonicalLESDiscriminatorSynthesisBoundary : LESDiscriminatorSynthesisBoundary
canonicalLESDiscriminatorSynthesisBoundary =
  lesDiscriminatorSynthesisBoundary false refl false refl true refl false refl
