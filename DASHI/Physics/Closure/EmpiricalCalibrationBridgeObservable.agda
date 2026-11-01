module DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservable where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- Option A: empirical-calibration bridge observable.
--
-- This module gives only the typed bridge shape from a total energy function
-- to a simple count/frequency/rate-like observable.  It does not provide an
-- empirical adequacy claim: promotion requires both a measured value and an
-- external authority token, and the current diagnostic below records that no
-- in-repo measured value is supplied by this module.

data SimpleObservableKind : Set where
  countLike :
    SimpleObservableKind
  frequencyLike :
    SimpleObservableKind
  rateLike :
    SimpleObservableKind

record SimpleObservableCarrier : Set₁ where
  field
    Carrier :
      Set

    kind :
      SimpleObservableKind

    observableOrder :
      Carrier → Carrier → Set

    carrierLabel :
      String

    orderLabel :
      String

------------------------------------------------------------------------
-- Authority and measurement requirements.

data EmpiricalCalibrationAuthorityToken : Set where

data MeasurementAvailability : Set where
  inRepoMeasuredValueSupplied :
    MeasurementAvailability
  noInRepoMeasuredValue :
    MeasurementAvailability

data EmpiricalCalibrationBlockedReason : Set where
  missingMeasuredValue :
    EmpiricalCalibrationBlockedReason
  missingExternalAuthorityToken :
    EmpiricalCalibrationBlockedReason
  adequacyNotClaimedByBridgeShape :
    EmpiricalCalibrationBlockedReason

data EmpiricalCalibrationAuthorityImpossibleHere : Set where

data ExternalMeasurementWitness : Set where

data ExternalAuthorityReceipt : Set where

empiricalCalibrationAuthorityImpossibleHere :
  EmpiricalCalibrationAuthorityToken →
  EmpiricalCalibrationAuthorityImpossibleHere
empiricalCalibrationAuthorityImpossibleHere ()

------------------------------------------------------------------------
-- Structural bridge surface.

record EmpiricalCalibrationBridgeObservableSurface : Setω where
  field
    State :
      Set

    E_total :
      State → Nat

    simpleObservable :
      SimpleObservableCarrier

    observable :
      State →
      SimpleObservableCarrier.Carrier simpleObservable

    energyToObservable :
      Nat →
      SimpleObservableCarrier.Carrier simpleObservable

    observableFactorsThroughEnergy :
      (s : State) →
      observable s
      ≡
      energyToObservable (E_total s)

    energyMonotonicityWitness :
      (x y : State) →
      E_total x ≤ E_total y →
      SimpleObservableCarrier.observableOrder simpleObservable
        (observable x)
        (observable y)

    measurementWitnessRequirement :
      Set

    externalAuthorityRequirement :
      Set

    nonPromotionBoundary :
      List String

record EmpiricalCalibrationBridgeObservableAdequacy
  (surface : EmpiricalCalibrationBridgeObservableSurface) : Setω where
  field
    authorityToken :
      EmpiricalCalibrationAuthorityToken

    measuredValue :
      SimpleObservableCarrier.Carrier
        (EmpiricalCalibrationBridgeObservableSurface.simpleObservable surface)

    measurementWitness :
      EmpiricalCalibrationBridgeObservableSurface.measurementWitnessRequirement
        surface

    externalAuthorityWitness :
      EmpiricalCalibrationBridgeObservableSurface.externalAuthorityRequirement
        surface

    calibratedState :
      EmpiricalCalibrationBridgeObservableSurface.State surface

    observableMatchesMeasuredValue :
      EmpiricalCalibrationBridgeObservableSurface.observable surface
        calibratedState
      ≡
      measuredValue

------------------------------------------------------------------------
-- Minimal Nat-valued count-like bridge shape.

natCountObservableCarrier :
  SimpleObservableCarrier
natCountObservableCarrier =
  record
    { Carrier =
        Nat
    ; kind =
        countLike
    ; observableOrder =
        _≤_
    ; carrierLabel =
        "Nat count/frequency/rate-like observable carrier"
    ; orderLabel =
        "Nat preorder used only as a simple observable order"
    }

minimalNatEnergyObservableSurface :
  EmpiricalCalibrationBridgeObservableSurface
minimalNatEnergyObservableSurface =
  record
    { State =
        Nat
    ; E_total =
        λ n → n
    ; simpleObservable =
        natCountObservableCarrier
    ; observable =
        λ n → n
    ; energyToObservable =
        λ n → n
    ; observableFactorsThroughEnergy =
        λ _ → refl
    ; energyMonotonicityWitness =
        λ _ _ energy≤ → energy≤
    ; measurementWitnessRequirement =
        ExternalMeasurementWitness
    ; externalAuthorityRequirement =
        ExternalAuthorityReceipt
    ; nonPromotionBoundary =
        "This is only an E_total-to-simple-observable bridge surface"
        ∷ "It supplies no measured empirical value"
        ∷ "It supplies no EmpiricalCalibrationAuthorityToken"
        ∷ "It does not claim empirical adequacy or promote W3/W4/W5"
        ∷ []
    }

record EmpiricalCalibrationBridgeObservableCurrentDiagnostic : Setω where
  field
    surface :
      EmpiricalCalibrationBridgeObservableSurface

    measurementAvailability :
      MeasurementAvailability

    blockedReasons :
      List EmpiricalCalibrationBlockedReason

    authorityTokenUninhabitedHere :
      EmpiricalCalibrationAuthorityToken →
      EmpiricalCalibrationAuthorityImpossibleHere

    diagnosticBoundary :
      List String

currentEmpiricalCalibrationBridgeObservableDiagnostic :
  EmpiricalCalibrationBridgeObservableCurrentDiagnostic
currentEmpiricalCalibrationBridgeObservableDiagnostic =
  record
    { surface =
        minimalNatEnergyObservableSurface
    ; measurementAvailability =
        noInRepoMeasuredValue
    ; blockedReasons =
        missingMeasuredValue
        ∷ missingExternalAuthorityToken
        ∷ adequacyNotClaimedByBridgeShape
        ∷ []
    ; authorityTokenUninhabitedHere =
        empiricalCalibrationAuthorityImpossibleHere
    ; diagnosticBoundary =
        "Option A bridge surface is typed as a minimal Nat observable over E_total"
        ∷ "No in-repo measured value is provided by this module"
        ∷ "No external calibration authority token is constructed by this module"
        ∷ "A downstream adequacy receipt must provide measuredValue, measurementWitness, authorityToken, and observableMatchesMeasuredValue"
        ∷ []
    }
