module DASHI.Environment.LESSequentialExperimentPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Core.SequentialRobustActionabilityPlannerExact as ActionPlan
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESDiscriminatorSynthesisExact as LESDiscriminator

------------------------------------------------------------------------
-- LES SEQUENTIAL EXPERIMENT PLANNER
--
-- Thin application layer over the repo-wide sequential planning kernels.  One
-- site/model state is the hypothesis/fine-world carrier; measurements come from
-- the declared LES measurement library; interventions are the mechanism's own
-- Control type.
------------------------------------------------------------------------

record LESSequentialConsumerExperiment
    {mechanism : Basis.DomainMechanismSocket}
    {Evidence Prediction : Set}
    (library : LESDiscriminator.LESMeasurementLibrary mechanism) : Set₂ where
  constructor lesSequentialConsumerExperiment
  field
    compatible : Envelope.Compatible Evidence (Basis.State mechanism)
    evidence : Evidence
    consumer : Basis.State mechanism → Prediction

    plan : Sequential.CertifiedSequentialPlan
      consumer
      (compatible evidence)

    everyAskedMeasurementDeclared : Set
    measurementCalibrationReference : String
    siteSpeciesSeasonReference : String
    consumerReference : String
    validationReference : String

open LESSequentialConsumerExperiment public

------------------------------------------------------------------------
-- Actionability-facing version.  The robust intervention system is supplied by
-- the application because Outcome ordering (`NoWorse`) is consumer/normative
-- semantics, not something the physical mechanism socket can invent.
------------------------------------------------------------------------

record LESSequentialActionabilityExperiment
    {mechanism : Basis.DomainMechanismSocket}
    {Outcome : Set}
    (system : Robust.HypothesisInterventionSystem
      (Basis.State mechanism) (Basis.Control mechanism) Outcome)
    (Authority : Basis.Control mechanism → Set)
    (live : Basis.State mechanism → Set) : Set₂ where
  constructor lesSequentialActionabilityExperiment
  field
    plan : ActionPlan.CertifiedSequentialActionabilityPlan
      system Authority live
    baselineControlReference : String
    outcomeOrderingReference : String
    interventionAuthorityReference : String
    measurementLibraryReference : String
    validationReference : String

open LESSequentialActionabilityExperiment public

record LESSequentialExperimentBoundary : Set where
  constructor lesSequentialExperimentBoundary
  field
    fixedMeasurementOrderRequired : Bool
    fixedMeasurementOrderRequiredIsFalse :
      fixedMeasurementOrderRequired ≡ false

    fullSPACStateIdentificationRequiredBeforeEveryControl : Bool
    fullSPACStateIdentificationRequiredBeforeEveryControlIsFalse :
      fullSPACStateIdentificationRequiredBeforeEveryControl ≡ false

    physicalMechanismAutomaticallySuppliesOutcomeValueOrdering : Bool
    physicalMechanismAutomaticallySuppliesOutcomeValueOrderingIsFalse :
      physicalMechanismAutomaticallySuppliesOutcomeValueOrdering ≡ false

    robustControlAutomaticallySuppliesInterventionAuthority : Bool
    robustControlAutomaticallySuppliesInterventionAuthorityIsFalse :
      robustControlAutomaticallySuppliesInterventionAuthority ≡ false

canonicalLESSequentialExperimentBoundary : LESSequentialExperimentBoundary
canonicalLESSequentialExperimentBoundary =
  lesSequentialExperimentBoundary
    false refl false refl false refl false refl
