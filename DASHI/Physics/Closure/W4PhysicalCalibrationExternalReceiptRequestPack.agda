module DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4PhysicalCalibrationRouteNarrowing as Route

------------------------------------------------------------------------
-- W4o physical-calibration external receipt request pack.
--
-- This module packages the exact provider-facing request for the Candidate256
-- physical calibration receipt.  It constructs no physical calibration
-- authority, unit system, dimensional law, spectra/bonding interpretation,
-- wet-lab evidence, physical validation, or W4 promotion.

data W4PhysicalCalibrationExternalReceiptRequestStatus : Set where
  blockedAwaitingCandidate256PhysicalCalibrationExternalReceipt :
    W4PhysicalCalibrationExternalReceiptRequestStatus

record W4PhysicalCalibrationProviderPayloadRequest : Setω where
  field
    currentStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    routeStatus :
      Route.W4PhysicalCalibrationRouteNarrowingCurrentStatus

    exactReceiptName :
      String

    exactAuthorityTokenName :
      String

    exactCalibrationGateName :
      String

    exactAuthorityArtifactRequirement :
      String

    exactMissingReceiptFields :
      List String

    blockedExternalFields :
      List External.Candidate256PhysicalCalibrationExternalBlockedField

    downstreamReceiptQueue :
      List External.W4PhysicalCalibrationExternalReceiptQueueItem

    downstreamReceiptQueueName :
      String

    blockedExternalFieldsAreCanonical :
      blockedExternalFields
      ≡
      External.canonicalCandidate256PhysicalCalibrationExternalBlockedFields

    blockedExternalFieldsAreCurrent :
      blockedExternalFields
      ≡
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.blockedExternalFields
        currentStatus

    routeMissingIngredients :
      List Route.W4PhysicalCalibrationRouteIngredient

    routeMissingIngredientsAreCanonical :
      routeMissingIngredients
      ≡
      Route.w4PhysicalCalibrationRouteNarrowedIngredients

    providerPayloadFields :
      List String

    providerInstructions :
      List String

    rejectedReceiptSubstitutes :
      List String

    routeBoundary :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

    impossibleAuthorityHere :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    impossibleReceiptHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

canonicalW4PhysicalCalibrationProviderPayloadRequest :
  W4PhysicalCalibrationProviderPayloadRequest
canonicalW4PhysicalCalibrationProviderPayloadRequest =
  record
    { currentStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; routeStatus =
        Route.canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus
    ; exactReceiptName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"
    ; exactAuthorityTokenName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationGate.Candidate256PhysicalCalibrationAuthorityToken"
    ; exactCalibrationGateName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationGate.Candidate256PhysicalCalibrationGate"
    ; exactAuthorityArtifactRequirement =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredAuthorityArtifact
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; exactMissingReceiptFields =
        "calibrationAuthority : Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "physicalUnitCarrier : Set"
        ∷ "physicalDimensionVector : structured SI-base exponent vector for the physical unit carrier"
        ∷ "natToUnitCalibrationMap : Nat -> physicalUnitCarrier"
        ∷ "calibratedQuotientScaleMap : Candidate256QuotientClass -> physicalUnitCarrier"
        ∷ "calibratedScaleMapFactorsThroughNat : calibratedQuotientScaleMap q == natToUnitCalibrationMap (candidate256SurrogateScale q)"
        ∷ "dimensionalPreservationLaw : QuotientLawAtWitness canonicalCandidate256QuotientLaw -> Set"
        ∷ "dimensionalPreservationAtWitness : every Candidate256 quotient-law witness inhabits dimensionalPreservationLaw"
        ∷ "physical unit, calibration-map, quotient-scale, factorization, and dimensional-preservation labels"
        ∷ []
    ; blockedExternalFields =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.blockedExternalFields
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; downstreamReceiptQueue =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.downstreamReceiptQueue
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; downstreamReceiptQueueName =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.downstreamReceiptQueueName
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; blockedExternalFieldsAreCanonical =
        refl
    ; blockedExternalFieldsAreCurrent =
        refl
    ; routeMissingIngredients =
        Route.w4PhysicalCalibrationRouteNarrowedIngredients
    ; routeMissingIngredientsAreCanonical =
        refl
    ; providerPayloadFields =
        "First obtain AcceptedDYLuminosityConventionAuthority for the DY luminosity/bin-integration convention"
        ∷ "Then establish W4ZAdequacy downstream of that accepted convention authority"
        ∷ "Then provide a physical unit carrier distinct from the dimensionless Nat surrogate"
        ∷ "Provide a structured SI-base dimension vector for the physical unit carrier"
        ∷ "Provide a Nat-to-physical-unit calibration map for Candidate256 surrogate scale values"
        ∷ "Provide a calibrated quotient-class scale map into the physical unit carrier"
        ∷ "Prove the calibrated quotient scale factors through candidate256SurrogateScale"
        ∷ "Provide dimensional preservation law and witness for the Candidate256 quotient law"
        ∷ "For the same-record Z-peak calibration anchor, provide checksum-bound t21 measurement and t22 covariance artifacts before any ratio-calibration law"
        ∷ "Preserve downstream boundary: spectra, bonding, wet-lab evidence, and empirical physical validation remain later receipts"
        ∷ []
    ; providerInstructions =
        "Use the exact Candidate256PhysicalCalibrationExternalReceipt type named above"
        ∷ "Treat AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt as the receipt queue"
        ∷ "Do not construct this receipt unless a legitimate external authority artifact already inhabits Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "Do not satisfy the request with Nat as its own promoted physical unit carrier"
        ∷ "Do not replace the dimension vector with prose unit labels"
        ∷ "Do not replace dimensional preservation with a label or prose unit annotation"
        ∷ "If no positive calibration receipt can be supplied, return a typed source/authority diagnostic instead of prose"
        ∷ []
    ; rejectedReceiptSubstitutes =
        "same-record HEPData t21/t22/t43/t44/t45/t46 anchors"
        ∷ "dirty Z-peak scalar shape-fit artifacts or chi2/dof improvements"
        ∷ "CT18/MSHT/LHAPDF packet probes not accepted by an external physical calibration authority"
        ∷ "Candidate256 quotient/cross-band witness terms before strict physical scale-setting"
        ∷ "strings, labels, citations, and provider diagnostics that do not inhabit Candidate256PhysicalCalibrationAuthorityToken"
        ∷ []
    ; routeBoundary =
        Route.W4PhysicalCalibrationRouteNarrowingCurrentStatus.routeBoundary
          Route.canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus
    ; nonPromotionBoundary =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.noPromotionBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; strictBlockerImpact =
        "W4 remains blocked first on AcceptedDYLuminosityConventionAuthority, then W4ZAdequacy, then Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "Candidate256PhysicalCalibrationAuthorityToken is constructorless in the current repo"
        ∷ "The current Candidate256 Nat surrogate remains dimensionless and non-promoting"
        ∷ "Scale-setting can discharge only after units, dimension vectors, calibration, factorization, and dimensional preservation are supplied"
        ∷ "Spectra, bonding, wet-lab evidence, and empirical physical validation remain downstream strict-physical lanes"
        ∷ []
    ; impossibleAuthorityHere =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.impossibleWithoutExternalAuthority
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; impossibleReceiptHere =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.impossibleReceiptWithoutExternalAuthority
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    }

record W4PhysicalCalibrationExternalReceiptRequestPack : Setω where
  field
    currentStatus :
      W4PhysicalCalibrationExternalReceiptRequestStatus

    currentExternalStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    routeNarrowingStatus :
      Route.W4PhysicalCalibrationRouteNarrowingCurrentStatus

    providerPayloadRequest :
      W4PhysicalCalibrationProviderPayloadRequest

    requiredNextReceipt :
      String

    downstreamReceiptQueue :
      List External.W4PhysicalCalibrationExternalReceiptQueueItem

    downstreamReceiptQueueName :
      String

    requiredExternalReceiptMatchesCurrent :
      requiredNextReceipt
      ≡
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredExternalReceipt
        currentExternalStatus

    consolidatedRequestBoundary :
      List String

    legitimateAuthorityArtifactBoundary :
      List String

    consolidatedStrictBlockerImpact :
      List String

canonicalW4PhysicalCalibrationExternalReceiptRequestPack :
  W4PhysicalCalibrationExternalReceiptRequestPack
canonicalW4PhysicalCalibrationExternalReceiptRequestPack =
  record
    { currentStatus =
        blockedAwaitingCandidate256PhysicalCalibrationExternalReceipt
    ; currentExternalStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; routeNarrowingStatus =
        Route.canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus
    ; providerPayloadRequest =
        canonicalW4PhysicalCalibrationProviderPayloadRequest
    ; requiredNextReceipt =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredExternalReceipt
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; downstreamReceiptQueue =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.downstreamReceiptQueue
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; downstreamReceiptQueueName =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.downstreamReceiptQueueName
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; requiredExternalReceiptMatchesCurrent =
        refl
    ; consolidatedRequestBoundary =
        "Request pack only aggregates W4 external receipt obligations and route narrowing into provider-facing fields"
        ∷ "Receipt queue is AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "It does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not construct Candidate256PhysicalCalibrationGate or strict physical closure"
        ∷ []
    ; legitimateAuthorityArtifactBoundary =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.legitimateAuthorityArtifactBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; consolidatedStrictBlockerImpact =
        W4PhysicalCalibrationProviderPayloadRequest.strictBlockerImpact
          canonicalW4PhysicalCalibrationProviderPayloadRequest
    }

canonicalW4PhysicalCalibrationRequestPackBlockedFields :
  List External.Candidate256PhysicalCalibrationExternalBlockedField
canonicalW4PhysicalCalibrationRequestPackBlockedFields =
  W4PhysicalCalibrationProviderPayloadRequest.blockedExternalFields
    canonicalW4PhysicalCalibrationProviderPayloadRequest

canonicalW4PhysicalCalibrationRequestPackRouteIngredients :
  List Route.W4PhysicalCalibrationRouteIngredient
canonicalW4PhysicalCalibrationRequestPackRouteIngredients =
  W4PhysicalCalibrationProviderPayloadRequest.routeMissingIngredients
    canonicalW4PhysicalCalibrationProviderPayloadRequest

canonicalW4PhysicalCalibrationRequestPackNonPromotionBoundary :
  List String
canonicalW4PhysicalCalibrationRequestPackNonPromotionBoundary =
  W4PhysicalCalibrationProviderPayloadRequest.nonPromotionBoundary
    canonicalW4PhysicalCalibrationProviderPayloadRequest
