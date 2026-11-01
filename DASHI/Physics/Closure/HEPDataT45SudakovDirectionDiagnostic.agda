module DASHI.Physics.Closure.HEPDataT45SudakovDirectionDiagnostic where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- HEP-R47: t45 Sudakov direction diagnostic.
--
-- The HEP-R46 high-mass holdout moved the t45 normalization into the right
-- range but left a shape failure: low-phi* bins were overpredicted and
-- high-phi* bins were underpredicted.  This file records the next diagnostic
-- convention only.  It is not a clean-freeze comparison-law receipt and it
-- does not promote W3/W4/W5/W8.

data SudakovDirectionConvention : Set where
  belowZPole : SudakovDirectionConvention
  aboveZPoleSignedLog : SudakovDirectionConvention

record HEPDataT45SudakovDirectionDiagnostic : Set where
  field
    t43Convention : SudakovDirectionConvention
    t45Convention : SudakovDirectionConvention

    previousT43Chi2PerDof : Float
    previousT45Chi2PerDof : Float

    -- HEP-R47 intentionally uses the sign that matches the measured t45
    -- residual direction: for an above-Z numerator, low-phi* predictions must
    -- move down and high-phi* predictions must move up.
    aboveZSignedLogLowersLowPhi : Bool
    aboveZSignedLogRaisesHighPhi : Bool

    implementationSurface : String

    -- Populated from the dirty diagnostic run after applying HEP-R47.
    t43Chi2PerDofAfterDirection : Float
    t45Chi2PerDofAfterDirection : Float
    t45MeanPredDataAfterDirection : Float

    -- Explicit governance boundary.
    statusNonPromoting : ⊤
    noPromotion : ⊤

canonicalHEPDataT45SudakovDirectionDiagnostic :
  HEPDataT45SudakovDirectionDiagnostic
canonicalHEPDataT45SudakovDirectionDiagnostic =
  record
    { t43Convention = belowZPole
    ; t45Convention = aboveZPoleSignedLog
    ; previousT43Chi2PerDof = 1.7408778006
    ; previousT45Chi2PerDof = 289.0582788838
    ; aboveZSignedLogLowersLowPhi = true
    ; aboveZSignedLogRaisesHighPhi = true
    ; implementationSurface =
        "DASHI.Physics.Prediction.sigma_dashi:_window_asymmetric_sudakov_ratio"
    ; t43Chi2PerDofAfterDirection = 1.7408778006
    ; t45Chi2PerDofAfterDirection = 16.1225593070
    ; t45MeanPredDataAfterDirection = 0.9587136559
    ; statusNonPromoting = tt
    ; noPromotion = tt
    }
