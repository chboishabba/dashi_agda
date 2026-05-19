module DASHI.Physics.Closure.Candidate256PhysicalCalibrationExternalReceipt where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4External
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Candidate256 physical calibration external receipt preflight.
--
-- This module records the exact dependency skeleton for the eventual
-- Candidate256 physical-calibration receipt:
--
--   AcceptedDYLuminosityConventionAuthority
--     -> W4ZAdequacyReceipt
--     -> Candidate256PhysicalCalibrationExternalReceipt
--
-- It constructs none of those positive dependencies in-repo.  The accepted DY
-- authority remains external, W4 Z adequacy remains external/downstream of
-- that authority, and the Candidate256 physical calibration authority token
-- remains the constructorless W4 gate token.

data Candidate256PhysicalCalibrationReceiptPreflightStatus : Set where
  blockedAwaitingAcceptedDYAuthorityAndW4ZAdequacy :
    Candidate256PhysicalCalibrationReceiptPreflightStatus

data AcceptedDYLuminosityConventionAuthority : Set where

acceptedDYLuminosityConventionAuthorityImpossibleHere :
  AcceptedDYLuminosityConventionAuthority →
  ⊥
acceptedDYLuminosityConventionAuthorityImpossibleHere ()

record W4ZAdequacyReceipt : Setω where
  field
    acceptedDYLuminosityConventionAuthority :
      AcceptedDYLuminosityConventionAuthority

    adequacyValidationPayload :
      List String

    zPeakAdequacyCitation :
      String

    adequacyBoundary :
      List String

w4ZAdequacyReceiptImpossibleHere :
  W4ZAdequacyReceipt →
  ⊥
w4ZAdequacyReceiptImpossibleHere receipt =
  acceptedDYLuminosityConventionAuthorityImpossibleHere
    (W4ZAdequacyReceipt.acceptedDYLuminosityConventionAuthority receipt)

record Candidate256PhysicalCalibrationExternalReceipt : Setω where
  field
    acceptedDYLuminosityConventionAuthority :
      AcceptedDYLuminosityConventionAuthority

    sourceW4ZAdequacyReceipt :
      W4ZAdequacyReceipt

    candidate256PhysicalCalibrationAuthority :
      Gate.Candidate256PhysicalCalibrationAuthorityToken

    unitCarrier :
      Set

    scaleMap :
      Nat →
      unitCarrier

    quotientScaleMap :
      Surrogate.Candidate256QuotientClass →
      unitCarrier

    candidate256CalibrationConstant :
      unitCarrier

    scaleMapFactorsThroughCandidate256Surrogate :
      (q : Surrogate.Candidate256QuotientClass) →
      quotientScaleMap q
      ≡
      scaleMap (Surrogate.candidate256SurrogateScale q)

    dimensionalPreservationLaw :
      Handoff.QuotientLawAtWitness
        Next.canonicalCandidate256QuotientLaw →
      Set

    dimensionalPreservationAtWitness :
      (law :
        Handoff.QuotientLawAtWitness
          Next.canonicalCandidate256QuotientLaw) →
      dimensionalPreservationLaw law

    externalAuthorityCitation :
      String

    validationPayload :
      List String

    sourceW4AdequacyReceiptName :
      String

    externalAuthorityBoundary :
      List String

candidate256PhysicalCalibrationExternalReceiptImpossibleHere :
  Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
candidate256PhysicalCalibrationExternalReceiptImpossibleHere receipt =
  acceptedDYLuminosityConventionAuthorityImpossibleHere
    (Candidate256PhysicalCalibrationExternalReceipt.acceptedDYLuminosityConventionAuthority
      receipt)

candidate256ReceiptToW4ExternalReceipt :
  Candidate256PhysicalCalibrationExternalReceipt →
  W4External.Candidate256PhysicalCalibrationExternalReceipt
candidate256ReceiptToW4ExternalReceipt receipt =
  record
    { calibrationAuthority =
        Candidate256PhysicalCalibrationExternalReceipt.candidate256PhysicalCalibrationAuthority
          receipt
    ; physicalUnitCarrier =
        Candidate256PhysicalCalibrationExternalReceipt.unitCarrier receipt
    ; natToUnitCalibrationMap =
        Candidate256PhysicalCalibrationExternalReceipt.scaleMap receipt
    ; calibratedQuotientScaleMap =
        Candidate256PhysicalCalibrationExternalReceipt.quotientScaleMap receipt
    ; calibratedScaleMapFactorsThroughNat =
        Candidate256PhysicalCalibrationExternalReceipt.scaleMapFactorsThroughCandidate256Surrogate
          receipt
    ; dimensionalPreservationLaw =
        Candidate256PhysicalCalibrationExternalReceipt.dimensionalPreservationLaw
          receipt
    ; dimensionalPreservationAtWitness =
        Candidate256PhysicalCalibrationExternalReceipt.dimensionalPreservationAtWitness
          receipt
    ; physicalUnitCarrierLabel =
        "Candidate256 externally accepted physical unit carrier"
    ; natToUnitCalibrationMapLabel =
        "Candidate256 Nat-surrogate to physical-unit scale map"
    ; calibratedQuotientScaleMapLabel =
        "Candidate256 quotient-class physical scale map"
    ; factorizationLabel =
        "Candidate256 quotient-scale map factors through candidate256SurrogateScale"
    ; dimensionalPreservationLabel =
        "Candidate256 dimensional preservation law for canonical quotient witness"
    }

data Candidate256PhysicalCalibrationPreflightMissing : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    Candidate256PhysicalCalibrationPreflightMissing
  missingW4ZAdequacyReceipt :
    Candidate256PhysicalCalibrationPreflightMissing
  missingCandidate256PhysicalCalibrationAuthority :
    Candidate256PhysicalCalibrationPreflightMissing
  missingUnitCarrier :
    Candidate256PhysicalCalibrationPreflightMissing
  missingScaleMap :
    Candidate256PhysicalCalibrationPreflightMissing
  missingCandidate256CalibrationConstant :
    Candidate256PhysicalCalibrationPreflightMissing
  missingDimensionalPreservationLaw :
    Candidate256PhysicalCalibrationPreflightMissing
  missingExternalAuthorityCitation :
    Candidate256PhysicalCalibrationPreflightMissing
  missingValidationPayload :
    Candidate256PhysicalCalibrationPreflightMissing

canonicalCandidate256PhysicalCalibrationPreflightMissing :
  List Candidate256PhysicalCalibrationPreflightMissing
canonicalCandidate256PhysicalCalibrationPreflightMissing =
  missingAcceptedDYLuminosityConventionAuthority
  ∷ missingW4ZAdequacyReceipt
  ∷ missingCandidate256PhysicalCalibrationAuthority
  ∷ missingUnitCarrier
  ∷ missingScaleMap
  ∷ missingCandidate256CalibrationConstant
  ∷ missingDimensionalPreservationLaw
  ∷ missingExternalAuthorityCitation
  ∷ missingValidationPayload
  ∷ []

record Candidate256PhysicalCalibrationReceiptPreflight : Setω where
  field
    status :
      Candidate256PhysicalCalibrationReceiptPreflightStatus

    currentW4ExternalStatus :
      W4External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    dependencyChainName :
      String

    dependencySkeleton :
      List String

    requiredReceiptFields :
      List String

    missingDependencies :
      List Candidate256PhysicalCalibrationPreflightMissing

    sourceW4AdequacyReceiptFieldName :
      String

    externalAuthorityBoundary :
      List String

    noCalibrationPromotionBoundary :
      List String

    downstreamBoundary :
      List String

    acceptedDYAuthorityImpossibleHere :
      AcceptedDYLuminosityConventionAuthority →
      ⊥

    preflightW4ZAdequacyReceiptImpossibleHere :
      W4ZAdequacyReceipt →
      ⊥

    candidate256ReceiptImpossibleHere :
      Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

canonicalCandidate256PhysicalCalibrationReceiptPreflight :
  Candidate256PhysicalCalibrationReceiptPreflight
canonicalCandidate256PhysicalCalibrationReceiptPreflight =
  record
    { status =
        blockedAwaitingAcceptedDYAuthorityAndW4ZAdequacy
    ; currentW4ExternalStatus =
        W4External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; dependencyChainName =
        "AcceptedDYLuminosityConventionAuthority + W4ZAdequacyReceipt -> Candidate256PhysicalCalibrationExternalReceipt"
    ; dependencySkeleton =
        "AcceptedDYLuminosityConventionAuthority : external accepted DY luminosity/bin-integration convention authority"
        ∷ "W4ZAdequacyReceipt : source adequacy receipt downstream of the accepted DY convention"
        ∷ "Candidate256PhysicalCalibrationExternalReceipt : unit carrier, scale map, calibration constant, dimensional law, citation, validation payload, and source W4 adequacy receipt"
        ∷ []
    ; requiredReceiptFields =
        "unitCarrier : Set"
        ∷ "scaleMap : Nat -> unitCarrier"
        ∷ "quotientScaleMap : Candidate256QuotientClass -> unitCarrier"
        ∷ "candidate256CalibrationConstant : unitCarrier"
        ∷ "scaleMapFactorsThroughCandidate256Surrogate : quotientScaleMap q == scaleMap (candidate256SurrogateScale q)"
        ∷ "dimensionalPreservationLaw : QuotientLawAtWitness canonicalCandidate256QuotientLaw -> Set"
        ∷ "externalAuthorityCitation : String"
        ∷ "validationPayload : List String"
        ∷ "sourceW4ZAdequacyReceipt : W4ZAdequacyReceipt"
        ∷ []
    ; missingDependencies =
        canonicalCandidate256PhysicalCalibrationPreflightMissing
    ; sourceW4AdequacyReceiptFieldName =
        "sourceW4ZAdequacyReceipt"
    ; externalAuthorityBoundary =
        "AcceptedDYLuminosityConventionAuthority has no constructor in this module"
        ∷ "W4ZAdequacyReceipt cannot be supplied without AcceptedDYLuminosityConventionAuthority"
        ∷ "Candidate256PhysicalCalibrationAuthorityToken remains constructorless in W4PhysicalCalibrationGate"
        ∷ "Citations, labels, and local diagnostics do not inhabit the authority tokens"
        ∷ []
    ; noCalibrationPromotionBoundary =
        "This preflight does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This preflight does not construct W4External.Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "The Candidate256 Nat surrogate remains dimensionless"
        ∷ "No matter-field or stress-energy handoff is made here"
        ∷ []
    ; downstreamBoundary =
        "Candidate256 calibration is prerequisite to matter and stress-energy receipts"
        ∷ "Matter and stress-energy lanes consume only a later positive calibration receipt"
        ∷ "Spectra, bonding, and empirical physical validation remain downstream of this preflight"
        ∷ []
    ; acceptedDYAuthorityImpossibleHere =
        acceptedDYLuminosityConventionAuthorityImpossibleHere
    ; preflightW4ZAdequacyReceiptImpossibleHere =
        w4ZAdequacyReceiptImpossibleHere
    ; candidate256ReceiptImpossibleHere =
        candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    }
