module DASHI.Environment.WaterHyacinthLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.BiocontrolExternalityExperimentExact as Experiment

------------------------------------------------------------------------
-- Thin LES-facing scenario.  The empirical values are fixture coordinates,
-- not claims that the formal layer has itself measured an ecosystem.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  unresolved supported : EvidenceStatus

data RestorationStatus : Set where
  controlOnly controlPlusRestoration : RestorationStatus

data PostReleaseSafetyStatus : Set where
  postReleaseUnresolved postReleaseObserved : PostReleaseSafetyStatus

data NetEcosystemStatus : Set where
  netOutcomeUnresolved netOutcomeSupported : NetEcosystemStatus

record WaterHyacinthInterventionScenario : Set where
  constructor waterHyacinthInterventionScenario
  field
    world : Experiment.InterventionWorld
    hostSpecificityEvidence : EvidenceStatus
    observedPostReleaseSafety : PostReleaseSafetyStatus
    restorationStatus : RestorationStatus
    netEcosystemBenefit : NetEcosystemStatus
    sourceReference : String
    evidenceBoundaryReference : String

open WaterHyacinthInterventionScenario public

canonicalWaterHyacinthScenario : WaterHyacinthInterventionScenario
canonicalWaterHyacinthScenario = waterHyacinthInterventionScenario
  Experiment.oxygenDebtWorld
  supported
  postReleaseObserved
  controlOnly
  netOutcomeUnresolved
  "CSIRO water-hyacinth biocontrol page plus Australian Weed Management Guide; empirical source coordinates only"
  "host specificity, observed post-release safety, restoration and net ecosystem benefit remain distinct evidence/status axes"

------------------------------------------------------------------------
-- Control and restoration are separate coordinates.
------------------------------------------------------------------------

record ControlRestorationSeparation : Set where
  constructor controlRestorationSeparation
  field
    targetControlPresent : Experiment.suppression (world canonicalWaterHyacinthScenario)
      ≡ Experiment.targetSuppressed
    restorationNotImplied : restorationStatus canonicalWaterHyacinthScenario ≡ controlOnly

canonicalControlRestorationSeparation : ControlRestorationSeparation
canonicalControlRestorationSeparation = controlRestorationSeparation refl refl

------------------------------------------------------------------------
-- Host-specificity evidence, field safety observation, and net ecosystem
-- benefit are intentionally non-collapsed status axes.
------------------------------------------------------------------------

record BiocontrolStatusSeparation : Set where
  constructor biocontrolStatusSeparation
  field
    hostSpecificityPaid : hostSpecificityEvidence canonicalWaterHyacinthScenario ≡ supported
    postReleaseSafetyObserved :
      observedPostReleaseSafety canonicalWaterHyacinthScenario ≡ postReleaseObserved
    netBenefitStillUnresolved :
      netEcosystemBenefit canonicalWaterHyacinthScenario ≡ netOutcomeUnresolved

canonicalBiocontrolStatusSeparation : BiocontrolStatusSeparation
canonicalBiocontrolStatusSeparation = biocontrolStatusSeparation refl refl refl

------------------------------------------------------------------------
-- Source boundary: source rows can pay provenance/evidence coordinates but do
-- not manufacture theoremhood, causal completeness, or deployment authority.
------------------------------------------------------------------------

record WaterHyacinthSourceBoundary : Set where
  constructor waterHyacinthSourceBoundary
  field
    sourceReferencePresent : String
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    sourceCreatesDeploymentAuthority : Bool
    sourceCreatesDeploymentAuthorityIsFalse : sourceCreatesDeploymentAuthority ≡ false
    controlEqualsRestoration : Bool
    controlEqualsRestorationIsFalse : controlEqualsRestoration ≡ false

canonicalWaterHyacinthSourceBoundary : WaterHyacinthSourceBoundary
canonicalWaterHyacinthSourceBoundary = waterHyacinthSourceBoundary
  "CSIRO/ENTO water-hyacinth biological control page; Australian Weed Management Guide - Water Hyacinth"
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Concrete externality coordinates carried into LES-facing planning.
------------------------------------------------------------------------

record LESExternalityCoordinates : Set where
  constructor lesExternalityCoordinates
  field
    biomassFate : Experiment.BiomassFate
    dissolvedOxygen : Experiment.OxygenState
    nutrientResidual : Experiment.NutrientResidual
    seedbankResidual : Experiment.SeedbankResidual
    replacementCommunity : Experiment.CommunityState
    nonTargetEvidence : Experiment.NonTargetState
    agentInteraction : Experiment.AgentInteraction

canonicalLESExternalityCoordinates : LESExternalityCoordinates
canonicalLESExternalityCoordinates = lesExternalityCoordinates
  (Experiment.biomassFate Experiment.oxygenDebtWorld)
  (Experiment.oxygen Experiment.oxygenDebtWorld)
  (Experiment.nutrientResidual Experiment.oxygenDebtWorld)
  (Experiment.seedbankResidual Experiment.oxygenDebtWorld)
  (Experiment.community Experiment.oxygenDebtWorld)
  (Experiment.nonTarget Experiment.oxygenDebtWorld)
  (Experiment.interaction Experiment.oxygenDebtWorld)
