module DASHI.Interop.PNFResidualConsumerReceiptRequestPack where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFResidualConsumerNextObligation as W6
import DASHI.Interop.SensibLawResidualLattice as Residual
import Ontology.Hecke.PNFResidualBridge as Hecke

------------------------------------------------------------------------
-- W6g runtime receipt handoff request pack.
--
-- This module consolidates the exact runtime fields that W6 still needs.
-- It is only a request surface: it does not construct PNFEmissionReceipt
-- values, classify atoms, assign wrappers/qualifiers/roles, compute labels by
-- inspection, or fabricate a Hecke candidate-pool receipt.

record PNFResidualConsumerRuntimeReceiptPayload : Set where
  field
    consumerProfile :
      String

    runtimeReceiptId :
      String

    leftEmissionReceipt :
      Residual.PNFEmissionReceipt

    rightEmissionReceipt :
      Residual.PNFEmissionReceipt

    heckeCandidatePoolReceiptId :
      String

payloadResidual :
  PNFResidualConsumerRuntimeReceiptPayload →
  Residual.ResidualLevel
payloadResidual payload =
  Residual.receiptResidual
    (PNFResidualConsumerRuntimeReceiptPayload.leftEmissionReceipt payload)
    (PNFResidualConsumerRuntimeReceiptPayload.rightEmissionReceipt payload)

payloadResidualIsReceiptBacked :
  (payload : PNFResidualConsumerRuntimeReceiptPayload) →
  payloadResidual payload
  ≡
  Residual.receiptResidual
    (PNFResidualConsumerRuntimeReceiptPayload.leftEmissionReceipt payload)
    (PNFResidualConsumerRuntimeReceiptPayload.rightEmissionReceipt payload)
payloadResidualIsReceiptBacked payload = refl

payloadToConsumerReceipt :
  PNFResidualConsumerRuntimeReceiptPayload →
  W6.PNFResidualConsumerReceipt
payloadToConsumerReceipt payload =
  W6.pnfResidualConsumerReceiptFromRuntimeEvidence
    (PNFResidualConsumerRuntimeReceiptPayload.consumerProfile payload)
    (PNFResidualConsumerRuntimeReceiptPayload.runtimeReceiptId payload)
    (PNFResidualConsumerRuntimeReceiptPayload.leftEmissionReceipt payload)
    (PNFResidualConsumerRuntimeReceiptPayload.rightEmissionReceipt payload)
    (PNFResidualConsumerRuntimeReceiptPayload.heckeCandidatePoolReceiptId payload)

payloadLeftAtomIsReceiptBacked :
  (payload : PNFResidualConsumerRuntimeReceiptPayload) →
  W6.PNFResidualConsumerReceipt.emittedLeftAtom
    (payloadToConsumerReceipt payload)
  ≡
  Residual.PNFEmissionReceipt.emittedAtom
    (PNFResidualConsumerRuntimeReceiptPayload.leftEmissionReceipt payload)
payloadLeftAtomIsReceiptBacked payload = refl

payloadRightAtomIsReceiptBacked :
  (payload : PNFResidualConsumerRuntimeReceiptPayload) →
  W6.PNFResidualConsumerReceipt.emittedRightAtom
    (payloadToConsumerReceipt payload)
  ≡
  Residual.PNFEmissionReceipt.emittedAtom
    (PNFResidualConsumerRuntimeReceiptPayload.rightEmissionReceipt payload)
payloadRightAtomIsReceiptBacked payload = refl

payloadConsumerResidualIsReceiptBacked :
  (payload : PNFResidualConsumerRuntimeReceiptPayload) →
  W6.PNFResidualConsumerReceipt.residualLevel
    (payloadToConsumerReceipt payload)
  ≡
  payloadResidual payload
payloadConsumerResidualIsReceiptBacked payload = refl

record PNFResidualConsumerReceiptRequestPack : Setω where
  field
    intakeRequest :
      W6.PNFResidualConsumerRuntimeIntakeRequest

    sourceDiagnostic :
      W6.PNFResidualConsumerRuntimeReceiptSourceDiagnostic

    requiredRuntimeFields :
      List W6.PNFResidualConsumerRuntimeSuppliedField

    derivedOnlyAfterRuntimeIntake :
      List W6.PNFResidualConsumerDerivedReceiptField

    nonInspectionBoundaries :
      List W6.PNFResidualConsumerNonInspectionBoundary

    receiptBuilder :
      PNFResidualConsumerRuntimeReceiptPayload →
      W6.PNFResidualConsumerReceipt

    receiptBackedResidualComputation :
      PNFResidualConsumerRuntimeReceiptPayload →
      Residual.ResidualLevel

    heckeBridgeSurface :
      Hecke.HeckePNFResidualBridgeSurface

    heckeCandidatePoolBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalPNFResidualConsumerReceiptRequestPack :
  PNFResidualConsumerReceiptRequestPack
canonicalPNFResidualConsumerReceiptRequestPack =
  record
    { intakeRequest =
        W6.canonicalPNFResidualConsumerRuntimeIntakeRequest
    ; sourceDiagnostic =
        W6.canonicalPNFResidualConsumerRuntimeReceiptSourceDiagnostic
    ; requiredRuntimeFields =
        W6.canonicalPNFResidualConsumerRuntimeSuppliedFields
    ; derivedOnlyAfterRuntimeIntake =
        W6.canonicalPNFResidualConsumerDerivableFields
    ; nonInspectionBoundaries =
        W6.PNFResidualConsumerMissingReceiptDiagnostic.nonInspectionBoundaries
          W6.canonicalPNFResidualConsumerMissingReceiptDiagnostic
    ; receiptBuilder =
        payloadToConsumerReceipt
    ; receiptBackedResidualComputation =
        payloadResidual
    ; heckeBridgeSurface =
        Hecke.heckePNFResidualBridgeSurface
    ; heckeCandidatePoolBoundary =
        Hecke.HeckePNFResidualBridgeSurface.nonClaimBoundary
          Hecke.heckePNFResidualBridgeSurface
    ; strictBlockerImpact =
        "Blocked until runtime supplies consumer profile and runtime receipt id"
        ∷ "Blocked until runtime supplies paired PNFEmissionReceipt values"
        ∷ "Blocked until runtime supplies the Hecke candidate-pool receipt id"
        ∷ "After those values arrive, emitted atoms and residual level derive from receipt fields by refl"
        ∷ "No runtime receipt, atom label, residual label, or Hecke fibre label is fabricated here"
        ∷ []
    }

canonicalRequestPackRequiredFields :
  List W6.PNFResidualConsumerRuntimeSuppliedField
canonicalRequestPackRequiredFields =
  PNFResidualConsumerReceiptRequestPack.requiredRuntimeFields
    canonicalPNFResidualConsumerReceiptRequestPack

canonicalRequestPackStrictBlockerImpact :
  List String
canonicalRequestPackStrictBlockerImpact =
  PNFResidualConsumerReceiptRequestPack.strictBlockerImpact
    canonicalPNFResidualConsumerReceiptRequestPack
