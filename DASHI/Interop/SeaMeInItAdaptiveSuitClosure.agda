module DASHI.Interop.SeaMeInItAdaptiveSuitClosure where

------------------------------------------------------------------------
-- Physical ROM validation -> adaptive module -> controller -> deployment
--
-- The upstream physical closure proves only the declared body/suit/ROM
-- measurement slice.  It does not grant authority to actuators, controllers,
-- or field deployment.  Those authorities are carried by distinct receipts
-- and an explicit external review gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)

open import DASHI.Interop.SeaMeInItROMKernelFormalism
  using
    ( TriGate
    ; gateReject
    ; gateDiagnostic
    ; gateAdmissible
    ; PromotionState
    ; promotedArtifact
    ; promotionFromGates
    ; allAdmissible
    ; BodyCarrier
    ; KernelBasis
    ; ROMOperator
    ; SeamGraph
    ; SeamCutPanelization
    )

open import DASHI.Interop.SeaMeInItSeamDerivationFormalism
  using (FinishedSeamReceipt)

open import DASHI.Interop.SeaMeInItPhysicalSuitClosure
  using
    ( AssemblyReceipt
    ; WearFitReceipt
    ; PhysicalROMValidationReceipt
    ; physicalROMPromotionState
    )

------------------------------------------------------------------------
-- Adaptive hardware module authority
------------------------------------------------------------------------

record AdaptiveModuleReceipt
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    {finished : FinishedSeamReceipt body basis romOp graph panelization}
    {assembly : AssemblyReceipt finished}
    {wearFit : WearFitReceipt assembly}
    (physical : PhysicalROMValidationReceipt wearFit)
    : Set₁ where
  field
    physicalROMPromoted :
      physicalROMPromotionState physical ≡ promotedArtifact

    physicalROMReceiptHash : String
    moduleManifestHash : String
    sensorMapHash : String
    actuatorMapHash : String
    powerBudgetHash : String
    failSafeEvidenceHash : String

    moduleCount : Nat
    sensorCount : Nat
    actuatorCount : Nat

    commandEnvelopeViolationNumerator : Nat
    commandEnvelopeViolationDenominator : Nat
    commandEnvelopeThresholdNumerator : Nat
    commandEnvelopeThresholdDenominator : Nat

    failSafeTestCount : Nat
    failSafeFailureCount : Nat

    moduleInventoryGate : TriGate
    commandEnvelopeGate : TriGate
    failSafeGate : TriGate
    powerBudgetGate : TriGate
    evidenceGate : TriGate

    noAutomaticControllerAuthorityClaim : Bool

  strictAdaptiveModuleGates : List TriGate
  strictAdaptiveModuleGates =
    moduleInventoryGate
    ∷ commandEnvelopeGate
    ∷ failSafeGate
    ∷ powerBudgetGate
    ∷ evidenceGate
    ∷ []

  adaptiveModulePromotionState : PromotionState
  adaptiveModulePromotionState = promotionFromGates strictAdaptiveModuleGates

open AdaptiveModuleReceipt public

------------------------------------------------------------------------
-- Controller authority
------------------------------------------------------------------------

record ControllerSafetyReceipt
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    {finished : FinishedSeamReceipt body basis romOp graph panelization}
    {assembly : AssemblyReceipt finished}
    {wearFit : WearFitReceipt assembly}
    {physical : PhysicalROMValidationReceipt wearFit}
    (adaptive : AdaptiveModuleReceipt physical)
    : Set₁ where
  field
    adaptiveModulePromoted :
      adaptiveModulePromotionState adaptive ≡ promotedArtifact

    adaptiveModuleReceiptHash : String
    controllerArtifactHash : String
    safetyEnvelopeHash : String
    scenarioManifestHash : String
    controllerTestEvidenceHash : String

    scenarioCount : Nat
    hardViolationCount : Nat
    maxCommandLatency : Nat
    commandLatencyThreshold : Nat
    commandLatencyWithinThreshold : maxCommandLatency ≤ commandLatencyThreshold
    emergencyStopTestCount : Nat
    emergencyStopFailureCount : Nat

    scenarioCoverageGate : TriGate
    hardViolationGate : TriGate
    latencyGate : TriGate
    emergencyStopGate : TriGate
    controllerEvidenceGate : TriGate

    noUniversalClosedLoopSafetyClaim : Bool

  strictControllerGates : List TriGate
  strictControllerGates =
    scenarioCoverageGate
    ∷ hardViolationGate
    ∷ latencyGate
    ∷ emergencyStopGate
    ∷ controllerEvidenceGate
    ∷ []

  controllerPromotionState : PromotionState
  controllerPromotionState = promotionFromGates strictControllerGates

open ControllerSafetyReceipt public

------------------------------------------------------------------------
-- Deployment authority is intentionally external/non-derivable
------------------------------------------------------------------------

record SuitDeploymentReceipt
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    {finished : FinishedSeamReceipt body basis romOp graph panelization}
    {assembly : AssemblyReceipt finished}
    {wearFit : WearFitReceipt assembly}
    {physical : PhysicalROMValidationReceipt wearFit}
    {adaptive : AdaptiveModuleReceipt physical}
    (controller : ControllerSafetyReceipt adaptive)
    : Set₁ where
  field
    controllerPromoted :
      controllerPromotionState controller ≡ promotedArtifact

    controllerSafetyReceiptHash : String
    deploymentProfileHash : String
    deploymentEvidenceHash : String
    authorityReviewReceiptHash : String

    -- This gate is deliberately an input.  No theorem in this module derives
    -- it from physical/controller promotion.
    externalAuthorityReviewGate : TriGate
    deploymentProfileGate : TriGate
    deploymentEvidenceGate : TriGate
    claimBoundaryGate : TriGate

    deploymentIsProfileSpecific : Bool
    noAutomaticFieldAuthorityClaim : Bool

  strictDeploymentGates : List TriGate
  strictDeploymentGates =
    externalAuthorityReviewGate
    ∷ deploymentProfileGate
    ∷ deploymentEvidenceGate
    ∷ claimBoundaryGate
    ∷ []

  deploymentPromotionState : PromotionState
  deploymentPromotionState = promotionFromGates strictDeploymentGates

open SuitDeploymentReceipt public

record AdaptiveSuitDeploymentPromoted
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    {finished : FinishedSeamReceipt body basis romOp graph panelization}
    {assembly : AssemblyReceipt finished}
    {wearFit : WearFitReceipt assembly}
    {physical : PhysicalROMValidationReceipt wearFit}
    {adaptive : AdaptiveModuleReceipt physical}
    {controller : ControllerSafetyReceipt adaptive}
    (deployment : SuitDeploymentReceipt controller)
    : Set₁ where
  field
    stateIsPromoted : deploymentPromotionState deployment ≡ promotedArtifact
    allDeploymentGatesClear :
      allAdmissible (strictDeploymentGates deployment) ≡ true
    physicalWasPromoted : physicalROMPromotionState physical ≡ promotedArtifact
    adaptiveWasPromoted : adaptiveModulePromotionState adaptive ≡ promotedArtifact
    controllerWasPromoted : controllerPromotionState controller ≡ promotedArtifact
    externalReviewWasAdmissible :
      externalAuthorityReviewGate deployment ≡ gateAdmissible

open AdaptiveSuitDeploymentPromoted public

------------------------------------------------------------------------
-- Product-level compiler surface
------------------------------------------------------------------------

record ROMToAdaptiveSuitSurface : Set₁ where
  field
    BodyObject : Set
    ROMObject : Set
    GarmentPatternObject : Set
    PhysicalAssemblyObject : Set
    WearMeasurementObject : Set
    AdaptiveModuleObject : Set
    ControllerObject : Set
    DeploymentProfileObject : Set

    romToPatternReceipt : String
    patternToPhysicalReceipt : String
    physicalToAdaptiveModuleReceipt : String
    adaptiveModuleToControllerReceipt : String
    controllerToDeploymentReviewReceipt : String

    deploymentAuthorityIsNotDerivedFromPhysicsProof : Bool
    deploymentAuthorityIsNotDerivedFromControllerTests : Bool
    externalHumanOrRegulatoryReviewRemainsExplicit : Bool

open ROMToAdaptiveSuitSurface public
