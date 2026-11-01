module DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFit where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Option C: finite toy-fit bridge surface.
--
-- This module only types the mechanics of fitting a finite local dataset.
-- It intentionally does not construct, import, or imply any external
-- empirical authority for W3/W8-style promotion.

data ExternalEmpiricalAuthorityToken : Set where

data ToyFitAdequacyScope : Set where
  finiteDatasetToyFitOnly : ToyFitAdequacyScope
  externalEmpiricalAuthorityRequired : ToyFitAdequacyScope

data ToyFitNotExternalAuthority : Set where
  toyFitHasNoExternalReceipt : ToyFitNotExternalAuthority

externalAuthorityImpossibleHere :
  ExternalEmpiricalAuthorityToken →
  ToyFitNotExternalAuthority
externalAuthorityImpossibleHere ()

record ToyFitBoundaryReceipt : Set₁ where
  field
    scope : ToyFitAdequacyScope
    toyAdequacyClaim : String
    externalAuthorityClaim : String
    noExternalAuthorityToken :
      ExternalEmpiricalAuthorityToken →
      ToyFitNotExternalAuthority

open ToyFitBoundaryReceipt public

canonicalToyFitBoundaryReceipt : ToyFitBoundaryReceipt
canonicalToyFitBoundaryReceipt =
  record
    { scope = finiteDatasetToyFitOnly
    ; toyAdequacyClaim =
        "finite toy observations fit under the supplied residual threshold"
    ; externalAuthorityClaim =
        "external empirical authority remains a separate receipt obligation"
    ; noExternalAuthorityToken = externalAuthorityImpossibleHere
    }

------------------------------------------------------------------------
-- Finite observations and dataset-wide predicates

record FiniteToyObservation (Input Value : Set) : Set₁ where
  field
    sampleLabel : String
    input : Input
    measured : Value

open FiniteToyObservation public

data All {A : Set₁} (P : A → Set) : List A → Set₁ where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

------------------------------------------------------------------------
-- Generic toy empirical calibration bridge.

record EmpiricalCalibrationBridgeToyFit : Setω where
  field
    Input : Set
    Value : Set
    Residual : Set

    observations : List (FiniteToyObservation Input Value)

    calibration : Input → Input
    prediction : Input → Value
    residual : Value → Value → Residual
    threshold : Residual
    residualAccepted : Residual → Residual → Set

    calibratedPredictionLaw :
      (x : Input) →
      prediction (calibration x) ≡ prediction (calibration x)

    observationMismatch :
      FiniteToyObservation Input Value →
      Residual

    observationMismatchLaw :
      (obs : FiniteToyObservation Input Value) →
      observationMismatch obs
      ≡
      residual
        (prediction (calibration (FiniteToyObservation.input obs)))
        (FiniteToyObservation.measured obs)

    observationAccepted :
      FiniteToyObservation Input Value →
      Set

    observationAcceptedLaw :
      (obs : FiniteToyObservation Input Value) →
      observationAccepted obs
      ≡
      residualAccepted (observationMismatch obs) threshold

    datasetAccepted :
      All observationAccepted observations

    adequacyBoundary :
      ToyFitBoundaryReceipt

    toyFitDoesNotProvideExternalAuthority :
      ExternalEmpiricalAuthorityToken →
      ToyFitNotExternalAuthority

open EmpiricalCalibrationBridgeToyFit public

calibratedPrediction :
  (fit : EmpiricalCalibrationBridgeToyFit) →
  EmpiricalCalibrationBridgeToyFit.Input fit →
  EmpiricalCalibrationBridgeToyFit.Value fit
calibratedPrediction fit x =
  EmpiricalCalibrationBridgeToyFit.prediction fit
    (EmpiricalCalibrationBridgeToyFit.calibration fit x)

------------------------------------------------------------------------
-- Small Nat-valued toy instance.
--
-- This is deliberately synthetic: three finite observations are accepted
-- because their mismatch is definitionally zero against a zero threshold.

data ToyInput : Set where
  toyStart : ToyInput
  toyMiddle : ToyInput
  toyExit : ToyInput

toyCalibration : ToyInput → ToyInput
toyCalibration toyStart = toyStart
toyCalibration toyMiddle = toyMiddle
toyCalibration toyExit = toyExit

toyPrediction : ToyInput → Nat
toyPrediction toyStart = zero
toyPrediction toyMiddle = suc zero
toyPrediction toyExit = suc (suc zero)

toyResidual : Nat → Nat → Nat
toyResidual zero zero = zero
toyResidual (suc _) zero = suc zero
toyResidual zero (suc _) = suc zero
toyResidual (suc x) (suc y) = toyResidual x y

data NatResidualAccepted : Nat → Nat → Set where
  zeroWithinZero : NatResidualAccepted zero zero

toyObservation₀ : FiniteToyObservation ToyInput Nat
toyObservation₀ =
  record
    { sampleLabel = "toy-start"
    ; input = toyStart
    ; measured = zero
    }

toyObservation₁ : FiniteToyObservation ToyInput Nat
toyObservation₁ =
  record
    { sampleLabel = "toy-middle"
    ; input = toyMiddle
    ; measured = suc zero
    }

toyObservation₂ : FiniteToyObservation ToyInput Nat
toyObservation₂ =
  record
    { sampleLabel = "toy-exit"
    ; input = toyExit
    ; measured = suc (suc zero)
    }

toyDataset : List (FiniteToyObservation ToyInput Nat)
toyDataset =
  toyObservation₀ ∷ toyObservation₁ ∷ toyObservation₂ ∷ []

toyObservationMismatch :
  FiniteToyObservation ToyInput Nat →
  Nat
toyObservationMismatch obs =
  toyResidual
    (toyPrediction (toyCalibration (FiniteToyObservation.input obs)))
    (FiniteToyObservation.measured obs)

toyObservationAccepted :
  FiniteToyObservation ToyInput Nat →
  Set
toyObservationAccepted obs =
  NatResidualAccepted (toyObservationMismatch obs) zero

toyObservationMismatchLaw :
  (obs : FiniteToyObservation ToyInput Nat) →
  toyObservationMismatch obs
  ≡
  toyResidual
    (toyPrediction (toyCalibration (FiniteToyObservation.input obs)))
    (FiniteToyObservation.measured obs)
toyObservationMismatchLaw obs = refl

toyObservationAcceptedLaw :
  (obs : FiniteToyObservation ToyInput Nat) →
  toyObservationAccepted obs
  ≡
  NatResidualAccepted (toyObservationMismatch obs) zero
toyObservationAcceptedLaw obs = refl

toyDatasetAccepted :
  All toyObservationAccepted toyDataset
toyDatasetAccepted =
  zeroWithinZero ∷ zeroWithinZero ∷ zeroWithinZero ∷ []

canonicalEmpiricalCalibrationBridgeToyFit :
  EmpiricalCalibrationBridgeToyFit
canonicalEmpiricalCalibrationBridgeToyFit =
  record
    { Input = ToyInput
    ; Value = Nat
    ; Residual = Nat
    ; observations = toyDataset
    ; calibration = toyCalibration
    ; prediction = toyPrediction
    ; residual = toyResidual
    ; threshold = zero
    ; residualAccepted = NatResidualAccepted
    ; calibratedPredictionLaw = λ x → refl
    ; observationMismatch = toyObservationMismatch
    ; observationMismatchLaw = toyObservationMismatchLaw
    ; observationAccepted = toyObservationAccepted
    ; observationAcceptedLaw = toyObservationAcceptedLaw
    ; datasetAccepted = toyDatasetAccepted
    ; adequacyBoundary = canonicalToyFitBoundaryReceipt
    ; toyFitDoesNotProvideExternalAuthority =
        externalAuthorityImpossibleHere
    }

canonicalToyFitScope :
  ToyFitBoundaryReceipt.scope
    (EmpiricalCalibrationBridgeToyFit.adequacyBoundary
      canonicalEmpiricalCalibrationBridgeToyFit)
  ≡
  finiteDatasetToyFitOnly
canonicalToyFitScope = refl
