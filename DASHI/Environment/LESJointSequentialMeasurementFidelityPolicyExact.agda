module DASHI.Environment.LESJointSequentialMeasurementFidelityPolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESAdaptiveSPACModelSearchExact as SPAC

------------------------------------------------------------------------
-- LES JOINT MEASUREMENT / FIDELITY POLICY
--
-- The live hypothesis carrier is the actual fine LES mechanism state.  Model
-- fidelity is tracked independently as a tiered SPAC reduction candidate.
-- Measurements can refine the state fibre; a fidelity escalation cannot do so
-- without subsequently confronting observations.
------------------------------------------------------------------------

LESJointPolicy :
  ∀ {mechanism : Basis.DomainMechanismSocket}
    (system : Robust.HypothesisInterventionSystem
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)) →
  (Authority : Basis.Control mechanism → Set) →
  (Basis.State mechanism → Set) →
  SPAC.TieredSPACCandidate mechanism →
  Set₁
LESJointPolicy {mechanism} system Authority live model =
  Joint.JointSequentialPolicy
    system Authority
    (SPAC.TieredSPACCandidate mechanism)
    live model

measurementAsLESEvidenceMove :
  ∀ {mechanism : Basis.DomainMechanismSocket} →
  Synthesis.ExperimentBundle (Basis.State mechanism) →
  Joint.EvidenceMove (Basis.State mechanism)
measurementAsLESEvidenceMove = Joint.bundleAsEvidenceMove

------------------------------------------------------------------------
-- Counterexample-driven SPAC fidelity transitions.
-- The transition cost is an application measurement/resource estimate, not the
-- candidate's abstract cost rank.
------------------------------------------------------------------------

bucketToRichardsFidelityMove :
  ∀ {mechanism}
    (portfolio : SPAC.SPACReductionPortfolio mechanism) →
  Search.CandidateRefutation
    (SPAC.candidate (SPAC.bucket portfolio)) →
  (transitionCost : Nat) →
  String →
  Joint.FidelityMove
    (SPAC.TieredSPACCandidate mechanism)
    (SPAC.bucket portfolio)
bucketToRichardsFidelityMove portfolio failure transitionCost costReference =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      transitionCost
      "LES bucket -> Richards consumer-driven escalation"
      costReference
      "retained bucket counterexample")
    refl
    (SPAC.richards portfolio)
    "bucket model erased a future-relevant soil-hydraulic distinction"
    "candidate refutation supplied to bucketToRichardsFidelityMove"

richardsToSPACFidelityMove :
  ∀ {mechanism}
    (portfolio : SPAC.SPACReductionPortfolio mechanism) →
  Search.CandidateRefutation
    (SPAC.candidate (SPAC.richards portfolio)) →
  (transitionCost : Nat) →
  String →
  Joint.FidelityMove
    (SPAC.TieredSPACCandidate mechanism)
    (SPAC.richards portfolio)
richardsToSPACFidelityMove portfolio failure transitionCost costReference =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      transitionCost
      "LES Richards -> hydraulic SPAC consumer-driven escalation"
      costReference
      "retained Richards counterexample")
    refl
    (SPAC.spac portfolio)
    "soil-only model erased a future-relevant plant hydraulic distinction"
    "candidate refutation supplied to richardsToSPACFidelityMove"

spacToElectroBiogeochemicalFidelityMove :
  ∀ {mechanism}
    (portfolio : SPAC.SPACReductionPortfolio mechanism) →
  Search.CandidateRefutation
    (SPAC.candidate (SPAC.spac portfolio)) →
  (transitionCost : Nat) →
  String →
  Joint.FidelityMove
    (SPAC.TieredSPACCandidate mechanism)
    (SPAC.spac portfolio)
spacToElectroBiogeochemicalFidelityMove
    portfolio failure transitionCost costReference =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      transitionCost
      "LES hydraulic SPAC -> electro-biogeochemical SPAC escalation"
      costReference
      "retained hydraulic-SPAC counterexample")
    refl
    (SPAC.electroBiogeochemical portfolio)
    "hydraulic SPAC erased a future-relevant nutrient/electrochemical distinction"
    "candidate refutation supplied to spacToElectroBiogeochemicalFidelityMove"

------------------------------------------------------------------------
-- Campaign receipt: one policy may interleave measurements and fidelity moves
-- and may terminate early at a robust independently authorised control.
------------------------------------------------------------------------

record LESJointMeasurementFidelityCampaign
    (mechanism : Basis.DomainMechanismSocket)
    (portfolio : SPAC.SPACReductionPortfolio mechanism) : Set₂ where
  constructor lesJointMeasurementFidelityCampaign
  field
    system : Robust.HypothesisInterventionSystem
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)
    Authority : Basis.Control mechanism → Set
    live : Basis.State mechanism → Set
    initialModel : SPAC.TieredSPACCandidate mechanism
    policy : LESJointPolicy system Authority live initialModel
    worstCaseCostBound : Nat
    costCertificate : Joint.JointPolicyCostAtMost policy worstCaseCostBound
    measurementLibraryReference : String
    fidelityCostReference : String
    robustConsumerReference : String
    authorityReference : String
    heldOutValidationReference : String

open LESJointMeasurementFidelityCampaign public

record LESJointMeasurementFidelityBoundary : Set where
  constructor lesJointMeasurementFidelityBoundary
  field
    richerModelAutomaticallyShrinksEmpiricalStateFibre : Bool
    richerModelAutomaticallyShrinksEmpiricalStateFibreIsFalse :
      richerModelAutomaticallyShrinksEmpiricalStateFibre ≡ false

    measurementAndFidelityCanBeInterleavedByOutcome : Bool
    measurementAndFidelityCanBeInterleavedByOutcomeIsTrue :
      measurementAndFidelityCanBeInterleavedByOutcome ≡ true

    counterexampleCanJustifyRicherModelState : Bool
    counterexampleCanJustifyRicherModelStateIsTrue :
      counterexampleCanJustifyRicherModelState ≡ true

    robustAuthorisedControlMayStopBeforeMaximumFidelity : Bool
    robustAuthorisedControlMayStopBeforeMaximumFidelityIsTrue :
      robustAuthorisedControlMayStopBeforeMaximumFidelity ≡ true

canonicalLESJointMeasurementFidelityBoundary :
  LESJointMeasurementFidelityBoundary
canonicalLESJointMeasurementFidelityBoundary =
  lesJointMeasurementFidelityBoundary false refl true refl true refl true refl
