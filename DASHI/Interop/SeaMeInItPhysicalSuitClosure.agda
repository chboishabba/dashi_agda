module DASHI.Interop.SeaMeInItPhysicalSuitClosure where

------------------------------------------------------------------------
-- ROM -> manufactured suit -> physical ROM closure
--
-- This module extends the existing SeaMeInIt seam/pattern receipt surface past
-- digital manufacturing output.  A finished pattern is not treated as evidence
-- that a fabricated garment realizes the predicted geometry or fields.
-- Physical promotion therefore requires three further receipts:
--
--   FinishedSeamReceipt
--     -> AssemblyReceipt
--     -> WearFitReceipt
--     -> PhysicalROMValidationReceipt
--
-- C3/BT369 appears here as an explicit transport witness.  Its exact law is a
-- mathematical contract for the chosen address/phase transport.  The separate
-- transport gate remains empirical: inhabiting the law does not assert that a
-- real garment obeys C3 symmetry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

open import DASHI.Interop.SeaMeInItROMKernelFormalism
  using
    ( TriGate
    ; gateReject
    ; gateDiagnostic
    ; gateAdmissible
    ; PromotionState
    ; diagnosticOnly
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
  using
    ( FinishedSeamReceipt
    ; patternPromotionState
    )

------------------------------------------------------------------------
-- Physical assembly realization
------------------------------------------------------------------------

record AssemblyReceipt
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    (finished : FinishedSeamReceipt body basis romOp graph panelization)
    : Set₁ where
  field
    finishedPatternPromoted :
      patternPromotionState finished ≡ promotedArtifact

    finishedPatternReceiptHash : String
    manufacturedArtifactsHash : String
    assembledGeometryHash : String
    assemblyEvidenceHash : String
    materialLotHashes : List String

    pieceCount : Nat
    realizedSeamCount : Nat
    expectedSeamCount : Nat
    seamCountMatches : realizedSeamCount ≡ expectedSeamCount

    maxGeometryDeviation : Nat
    geometryDeviationThreshold : Nat
    geometryDeviationWithinThreshold :
      maxGeometryDeviation ≤ geometryDeviationThreshold

    geometryGate : TriGate
    materialProvenanceGate : TriGate
    assemblyEvidenceGate : TriGate

  strictAssemblyGates : List TriGate
  strictAssemblyGates =
    geometryGate
    ∷ materialProvenanceGate
    ∷ assemblyEvidenceGate
    ∷ []

  assemblyPromotionState : PromotionState
  assemblyPromotionState =
    promotionFromGates strictAssemblyGates

open AssemblyReceipt public

------------------------------------------------------------------------
-- Wear-fit residuals over a declared ROM/task slice
------------------------------------------------------------------------

record ResidualChannel : Set where
  field
    channel : String
    residual : Nat
    threshold : Nat
    residualWithinThreshold : residual ≤ threshold
    channelGate : TriGate

open ResidualChannel public

record WearFitReceipt
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    {finished : FinishedSeamReceipt body basis romOp graph panelization}
    (assembly : AssemblyReceipt finished)
    : Set₁ where
  field
    assemblyPromoted :
      assemblyPromotionState assembly ≡ promotedArtifact

    assemblyReceiptHash : String
    romReceiptHash : String
    taskProfileHash : String
    predictedFieldHash : String
    measuredFieldHash : String
    measurementEvidenceHash : String

    sampleCount : Nat
    taskCoverageNumerator : Nat
    taskCoverageDenominator : Nat
    residualChannels : List ResidualChannel

    sampleGate : TriGate
    taskCoverageGate : TriGate
    fieldResidualGate : TriGate
    measurementEvidenceGate : TriGate

  strictWearFitGates : List TriGate
  strictWearFitGates =
    sampleGate
    ∷ taskCoverageGate
    ∷ fieldResidualGate
    ∷ measurementEvidenceGate
    ∷ []

  wearFitPromotionState : PromotionState
  wearFitPromotionState =
    promotionFromGates strictWearFitGates

open WearFitReceipt public

------------------------------------------------------------------------
-- C3/BT369 transport contract
------------------------------------------------------------------------

record C3BT369TransportWitness : Set₁ where
  field
    transportModel : String
    addressSchema : String
    phaseProvenanceHash : String
    orientationReceiptHash : String

    transportPhase : C3.C3 → C3.C3
    c3Equivariant :
      (g x : C3.C3) →
      transportPhase (C3.act g x) ≡
      C3.act g (transportPhase x)

    transportEvidenceGate : TriGate

open C3BT369TransportWitness public

-- A mathematical identity transport is inhabited, but intentionally remains
-- diagnostic: it witnesses only that the C3 transport contract is coherent.
identityC3TransportDiagnostic : C3BT369TransportWitness
identityC3TransportDiagnostic = record
  { transportModel = "identity-c3-law-only"
  ; addressSchema = "no-physical-bt369-address-receipt"
  ; phaseProvenanceHash = "diagnostic-only"
  ; orientationReceiptHash = "diagnostic-only"
  ; transportPhase = λ x → x
  ; c3Equivariant = λ g x → refl
  ; transportEvidenceGate = gateDiagnostic
  }

------------------------------------------------------------------------
-- Physical closure back onto ROM
------------------------------------------------------------------------

record PhysicalROMValidationReceipt
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    {finished : FinishedSeamReceipt body basis romOp graph panelization}
    {assembly : AssemblyReceipt finished}
    (wearFit : WearFitReceipt assembly)
    : Set₁ where
  field
    wearFitPromoted :
      wearFitPromotionState wearFit ≡ promotedArtifact

    wearFitReceiptHash : String
    sourceROMReceiptHash : String
    calibratedROMReceiptHash : Maybe String
    validationEvidenceHash : String
    fieldResidualHash : String
    closureIteration : Nat

    triadicTransport : C3BT369TransportWitness

    physicalEvidenceGate : TriGate
    residualClosureGate : TriGate
    c3TransportGate : TriGate
    calibrationGate : TriGate
    claimBoundaryGate : TriGate

    plainReading : String
    noUniversalGarmentPhysicsClaim : Bool
    noClinicalSafetyClaim : Bool
    noAutomaticDeploymentAuthorityClaim : Bool

  strictPhysicalROMGates : List TriGate
  strictPhysicalROMGates =
    physicalEvidenceGate
    ∷ residualClosureGate
    ∷ c3TransportGate
    ∷ calibrationGate
    ∷ claimBoundaryGate
    ∷ []

  physicalROMPromotionState : PromotionState
  physicalROMPromotionState =
    promotionFromGates strictPhysicalROMGates

open PhysicalROMValidationReceipt public

------------------------------------------------------------------------
-- Promotion witnesses
------------------------------------------------------------------------

record PhysicalROMPromoted
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
    stateIsPromoted :
      physicalROMPromotionState physical ≡ promotedArtifact
    allPhysicalGatesClear :
      allAdmissible (strictPhysicalROMGates physical) ≡ true
    assemblyWasPromoted :
      assemblyPromotionState assembly ≡ promotedArtifact
    wearFitWasPromoted :
      wearFitPromotionState wearFit ≡ promotedArtifact
    c3TransportWasMeasured :
      C3BT369TransportWitness.transportEvidenceGate
        (triadicTransport physical)
      ≡ gateAdmissible

open PhysicalROMPromoted public

------------------------------------------------------------------------
-- End-to-end compiler surface
------------------------------------------------------------------------

record ROMToSuitClosureSurface : Set₁ where
  field
    BodyObject : Set
    ROMObject : Set
    FieldObject : Set
    SeamObject : Set
    PanelObject : Set
    PatternObject : Set
    AssemblyObject : Set
    WearMeasurementObject : Set
    PhysicalROMObject : Set

    romToFieldsReceipt : String
    fieldsToSeamsReceipt : String
    seamsToPanelsReceipt : String
    panelsToPatternReceipt : String
    patternToAssemblyReceipt : String
    assemblyToWearReceipt : String
    wearToPhysicalROMReceipt : String

    c3AddressTransportReceipt : String
    closureIsObservationAndTransportNotIdentityClaim : Bool
    productionDeploymentRequiresSeparateAuthority : Bool

open ROMToSuitClosureSurface public
