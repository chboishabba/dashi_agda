module DASHI.Physics.Closure.W4PhysicalCalibrationRouteNarrowing where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next

------------------------------------------------------------------------
-- W4n physical-calibration route narrowing.
--
-- This module does not construct physical units, calibration, validation,
-- or Candidate256PhysicalCalibrationAuthorityToken.  It narrows the next W4
-- route to one typed checklist and records the current state as blocked.

data W4PhysicalCalibrationRouteIngredient : Set where
  needsPhysicalUnitCarrier :
    W4PhysicalCalibrationRouteIngredient
  needsNatToPhysicalUnitCalibration :
    W4PhysicalCalibrationRouteIngredient
  needsQuotientScaleFactorization :
    W4PhysicalCalibrationRouteIngredient
  needsDimensionalPreservation :
    W4PhysicalCalibrationRouteIngredient
  needsPhysicalValidation :
    W4PhysicalCalibrationRouteIngredient

data W4PhysicalCalibrationRouteStatus : Set where
  blockedAwaitingTypedRouteIngredients :
    W4PhysicalCalibrationRouteStatus

data W4PhysicalCalibrationRouteClosureToken : Set where

record W4PhysicalCalibrationRouteNarrowingCurrentStatus : Setω where
  field
    gateStatus :
      Gate.Candidate256PhysicalCalibrationCurrentStatus

    externalReceiptStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    handoffPreReceipt :
      Handoff.ChemistryPhysicalHandoffPreReceipt

    strictNextReceipt :
      Next.Candidate256StrictPhysicalNextObligationReceipt

    currentRouteStatus :
      W4PhysicalCalibrationRouteStatus

    missingRouteIngredients :
      List W4PhysicalCalibrationRouteIngredient

    gateBlockedIngredients :
      List Gate.Candidate256PhysicalCalibrationBlockedIngredient

    externalBlockedFields :
      List External.Candidate256PhysicalCalibrationExternalBlockedField

    strictPhysicalMissingIngredients :
      List Blocker.StrictPhysicalMissingIngredient

    physicalUnitCarrierRequirement : String
    natToUnitCalibrationRequirement : String
    quotientScaleFactorizationRequirement : String
    dimensionalPreservationRequirement : String
    physicalValidationRequirement : String

    closureWouldNeed :
      W4PhysicalCalibrationRouteClosureToken →
      Set

    routeBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus :
  W4PhysicalCalibrationRouteNarrowingCurrentStatus
canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus =
  record
    { gateStatus =
        Gate.canonicalCandidate256PhysicalCalibrationCurrentStatus
    ; externalReceiptStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; handoffPreReceipt =
        Handoff.canonicalChemistryPhysicalHandoffPreReceipt
    ; strictNextReceipt =
        Next.canonicalCandidate256StrictPhysicalNextObligationReceipt
    ; currentRouteStatus =
        blockedAwaitingTypedRouteIngredients
    ; missingRouteIngredients =
        needsPhysicalUnitCarrier
        ∷ needsNatToPhysicalUnitCalibration
        ∷ needsQuotientScaleFactorization
        ∷ needsDimensionalPreservation
        ∷ needsPhysicalValidation
        ∷ []
    ; gateBlockedIngredients =
        Gate.Candidate256PhysicalCalibrationCurrentStatus.blockedIngredients
          Gate.canonicalCandidate256PhysicalCalibrationCurrentStatus
    ; externalBlockedFields =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.blockedExternalFields
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; strictPhysicalMissingIngredients =
        Next.Candidate256StrictPhysicalNextObligationReceipt.nextObligations
          Next.canonicalCandidate256StrictPhysicalNextObligationReceipt
    ; physicalUnitCarrierRequirement =
        "supply a physical unit carrier distinct from the dimensionless Nat surrogate"
    ; natToUnitCalibrationRequirement =
        "supply a Nat-to-physical-unit calibration map for the Candidate256 surrogate scale"
    ; quotientScaleFactorizationRequirement =
        "factor the calibrated quotient-scale map through the Nat surrogate scale"
    ; dimensionalPreservationRequirement =
        "prove dimensional preservation for the Candidate256 quotient law at the witness"
    ; physicalValidationRequirement =
        "supply the downstream spectra, bonding, and empirical physical-validation receipts"
    ; closureWouldNeed =
        λ token → W4PhysicalCalibrationRouteClosureToken
    ; routeBoundary =
        "The route is narrowed to: physical units, Nat-to-unit calibration, quotient-scale factorization, dimensional preservation, and physical validation"
        ∷ "The current gate and external receipt statuses remain obligation surfaces"
        ∷ "The current handoff remains pre-physical and pre-scale-setting"
        ∷ "The strict-next receipt still lists scale-setting, spectra, bonding, and empirical physical-validation obligations"
        ∷ []
    ; noPromotionBoundary =
        "W4PhysicalCalibrationRouteClosureToken has no constructor in this module"
        ∷ "No Candidate256PhysicalCalibrationAuthorityToken is constructed"
        ∷ "No Candidate256PhysicalCalibrationGate value is constructed"
        ∷ "No physical unit carrier, calibration map, dimensional law, spectra, bonding, or empirical validation is fabricated here"
        ∷ []
    }

w4PhysicalCalibrationRouteNarrowedIngredients :
  List W4PhysicalCalibrationRouteIngredient
w4PhysicalCalibrationRouteNarrowedIngredients =
  W4PhysicalCalibrationRouteNarrowingCurrentStatus.missingRouteIngredients
    canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus
