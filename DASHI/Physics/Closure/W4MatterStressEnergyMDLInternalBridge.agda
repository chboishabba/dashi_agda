module DASHI.Physics.Closure.W4MatterStressEnergyMDLInternalBridge where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Primitive using (Set; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

import MDL.Core.Core as OldMDL
import DASHI.MDL.MDLDescentTradeoff as MDL
import DASHI.Physics.RealTernaryCarrier as RTC
import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt as W4SE

------------------------------------------------------------------------
-- Internal MDL stress-energy bridge.
--
-- This module is intentionally weaker than W4MatterStressEnergyPromotion.
-- It inhabits an internal stress-energy-shaped interface from the current
-- shift Lyapunov/MDL surface.  It does not construct a W4 matter field from
-- physical calibration, does not prove an Einstein equation, and does not
-- reinterpret Lyapunov descent as exact physical conservation.

record InternalStressEnergyDiagonal : Set where
  field
    energyDensity :
      Nat

    pressureX :
      Nat

    pressureY :
      Nat

    pressureZ :
      Nat

data W4MatterStressEnergyAdapterStatus : Set where
  internalBridgeInhabitedPhysicalUnitsObstructed :
    W4MatterStressEnergyAdapterStatus
  physicallyDimensionedAdapterReceiptAvailable :
    W4MatterStressEnergyAdapterStatus

data W4MatterStressEnergyAdapterMissingField : Set where
  missingBaseUnit :
    W4MatterStressEnergyAdapterMissingField
  missingPhysicalUnitCarrier :
    W4MatterStressEnergyAdapterMissingField
  missingEnergyDensityDimension :
    W4MatterStressEnergyAdapterMissingField
  missingPressureDimension :
    W4MatterStressEnergyAdapterMissingField
  missingNatToPhysicalUnitCalibrationMap :
    W4MatterStressEnergyAdapterMissingField
  missingStressEnergyUnitBinding :
    W4MatterStressEnergyAdapterMissingField
  missingDiscreteConservationSubstitute :
    W4MatterStressEnergyAdapterMissingField
  missingConservationPromotionBoundary :
    W4MatterStressEnergyAdapterMissingField

canonicalW4MatterStressEnergyAdapterMissingFields :
  List W4MatterStressEnergyAdapterMissingField
canonicalW4MatterStressEnergyAdapterMissingFields =
  missingBaseUnit
  ∷ missingPhysicalUnitCarrier
  ∷ missingEnergyDensityDimension
  ∷ missingPressureDimension
  ∷ missingNatToPhysicalUnitCalibrationMap
  ∷ missingStressEnergyUnitBinding
  ∷ missingDiscreteConservationSubstitute
  ∷ missingConservationPromotionBoundary
  ∷ []

data W4MatterStressEnergyConservationPromotionObligation : Set where
  proveDiscreteDivergenceOrScopedSubstitute :
    W4MatterStressEnergyConservationPromotionObligation
  proveMonotoneLyapunovDescentIsOnlyADissipativeProxy :
    W4MatterStressEnergyConservationPromotionObligation
  preventCovariantConservationPromotion :
    W4MatterStressEnergyConservationPromotionObligation

canonicalConservationPromotionObligations :
  List W4MatterStressEnergyConservationPromotionObligation
canonicalConservationPromotionObligations =
  proveDiscreteDivergenceOrScopedSubstitute
  ∷ proveMonotoneLyapunovDescentIsOnlyADissipativeProxy
  ∷ preventCovariantConservationPromotion
  ∷ []

data W4MatterStressEnergyNoPromotionGuard : Set where
  noEinsteinLawPromotion :
    W4MatterStressEnergyNoPromotionGuard
  noGRPromotion :
    W4MatterStressEnergyNoPromotionGuard
  noCovariantConservationClaim :
    W4MatterStressEnergyNoPromotionGuard
  noCandidate256CalibrationEdit :
    W4MatterStressEnergyNoPromotionGuard
  noW4MatterStressEnergyPromotion :
    W4MatterStressEnergyNoPromotionGuard

canonicalW4MatterStressEnergyNoPromotionGuard :
  List W4MatterStressEnergyNoPromotionGuard
canonicalW4MatterStressEnergyNoPromotionGuard =
  noEinsteinLawPromotion
  ∷ noGRPromotion
  ∷ noCovariantConservationClaim
  ∷ noCandidate256CalibrationEdit
  ∷ noW4MatterStressEnergyPromotion
  ∷ []

record W4MatterStressEnergyPhysicalAdapterReceipt : Setω where
  field
    PhysicalUnitCarrier :
      Set

    baseUnit :
      PhysicalUnitCarrier

    energyDensityDimension :
      String

    pressureDimension :
      String

    natToPhysicalUnit :
      Nat →
      PhysicalUnitCarrier

    stressEnergyUnitBinding :
      InternalStressEnergyDiagonal →
      PhysicalUnitCarrier

    conservationPromotionObligation :
      List W4MatterStressEnergyConservationPromotionObligation

    adapterBoundary :
      List String

    promotesEinsteinLaw :
      Bool

    promotesGR :
      Bool

data W4MatterStressEnergyPhysicalAdapterReceiptUnavailable : Set where

physicalAdapterReceiptUnavailableHere :
  W4MatterStressEnergyPhysicalAdapterReceipt →
  W4MatterStressEnergyPhysicalAdapterReceiptUnavailable →
  ⊥
physicalAdapterReceiptUnavailableHere _ ()

record W4MatterStressEnergyAdapterObstruction : Setω where
  field
    status :
      W4MatterStressEnergyAdapterStatus

    internalBridge :
      InternalStressEnergyDiagonal →
      InternalStressEnergyDiagonal

    tsfvCalibrationDiagnostic :
      TSFV.TSFVCandidate256CalibrationLawDiagnostic

    tsfvLawConstructedHere :
      TSFV.TSFVCandidate256CalibrationLawDiagnostic.constructsTSFVCalibrationLaw
        tsfvCalibrationDiagnostic
      ≡
      false

    candidate256ExternalReceiptConstructedHere :
      TSFV.TSFVCandidate256CalibrationLawDiagnostic.constructsCandidate256PhysicalCalibrationExternalReceipt
        tsfvCalibrationDiagnostic
      ≡
      false

    missingFields :
      List W4MatterStressEnergyAdapterMissingField

    missingFieldsAreCanonical :
      missingFields
      ≡
      canonicalW4MatterStressEnergyAdapterMissingFields

    unitBinding :
      String

    energyDensityDimensionTarget :
      String

    pressureDimensionTarget :
      String

    exactBaseUnitObstruction :
      String

    exactConservationPromotionObligation :
      List W4MatterStressEnergyConservationPromotionObligation

    exactConservationPromotionObligationIsCanonical :
      exactConservationPromotionObligation
      ≡
      canonicalConservationPromotionObligations

    noPromotionGuard :
      List W4MatterStressEnergyNoPromotionGuard

    noPromotionGuardIsCanonical :
      noPromotionGuard
      ≡
      canonicalW4MatterStressEnergyNoPromotionGuard

    physicalAdapterReceiptBlocked :
      W4MatterStressEnergyPhysicalAdapterReceipt →
      W4MatterStressEnergyPhysicalAdapterReceiptUnavailable →
      ⊥

canonicalW4MatterStressEnergyAdapterObstruction :
  W4MatterStressEnergyAdapterObstruction
canonicalW4MatterStressEnergyAdapterObstruction =
  record
    { status =
        internalBridgeInhabitedPhysicalUnitsObstructed
    ; internalBridge =
        λ diagonal → diagonal
    ; tsfvCalibrationDiagnostic =
        TSFV.canonicalTSFVCandidate256CalibrationLawDiagnostic
    ; tsfvLawConstructedHere =
        refl
    ; candidate256ExternalReceiptConstructedHere =
        refl
    ; missingFields =
        canonicalW4MatterStressEnergyAdapterMissingFields
    ; missingFieldsAreCanonical =
        refl
    ; unitBinding =
        "No PhysicalUnitCarrier/baseUnit binding is available for the Nat-valued MDL Lyapunov J or pressure proxy"
    ; energyDensityDimensionTarget =
        "energy density dimension required for rho = unit(J) over the physical adapter, not Nat"
    ; pressureDimensionTarget =
        "pressure/stress dimension required for p_i = unit(proxy_i), not Nat"
    ; exactBaseUnitObstruction =
        "baseUnit is blocked on TSFVTritCalibrationLaw.PhysicalUnitCarrier/baseUnit and Candidate256PhysicalCalibrationAuthorityToken; diagnostic TSFVDiagnosticPhysicalUnitCarrier is not an external W4 authority"
    ; exactConservationPromotionObligation =
        canonicalConservationPromotionObligations
    ; exactConservationPromotionObligationIsCanonical =
        refl
    ; noPromotionGuard =
        canonicalW4MatterStressEnergyNoPromotionGuard
    ; noPromotionGuardIsCanonical =
        refl
    ; physicalAdapterReceiptBlocked =
        physicalAdapterReceiptUnavailableHere
    }

record InternalMDLStressEnergyInterface : Setω where
  field
    State :
      Set

    step :
      State →
      State

    lyapunov :
      OldMDL.Lyapunov step

    MatterField :
      Set

    matterFromState :
      State →
      MatterField

    StressEnergyTensor :
      MatterField →
      Set

    stressEnergyFromState :
      (state : State) →
      StressEnergyTensor (matterFromState state)

    energyDensityFromState :
      State →
      Nat

    isotropicPressureProxy :
      State →
      Nat

    stressEnergyDiagonal :
      State →
      InternalStressEnergyDiagonal

    lyapunovEnergyMatchesDensity :
      (state : State) →
      energyDensityFromState state
      ≡
      OldMDL.Lyapunov.L lyapunov state

    energyDensityDescent :
      (state : State) →
      energyDensityFromState (step state)
      ≤
      energyDensityFromState state

    interfaceBoundary :
      List String

record InternalMDLStressEnergyBridgeReceipt : Setω where
  field
    m :
      Nat

    k :
      Nat

    internalInterface :
      InternalMDLStressEnergyInterface

    sourceLyapunovName :
      String

    sourceStateName :
      String

    proposedAdapterStatus :
      List String

    adapterObstruction :
      W4MatterStressEnergyAdapterObstruction

    exactObstructionToW4Promotion :
      List String

    noW4Promotion :
      W4SE.W4MatterStressEnergyPromotion →
      ⊥

internalShiftMDLStressEnergyInterface :
  (m k : Nat) →
  InternalMDLStressEnergyInterface
internalShiftMDLStressEnergyInterface m k =
  let
    Parts =
      MSI.MDLPartsShift {m} {k}

    lyap =
      MDLL.lyapunovShift {m} {k}
  in
  record
    { State =
        RTC.Carrier (m + k)
    ; step =
        MDL.MDLParts.T Parts
    ; lyapunov =
        lyap
    ; MatterField =
        RTC.Carrier (m + k)
    ; matterFromState =
        λ state → state
    ; StressEnergyTensor =
        λ _ → InternalStressEnergyDiagonal
    ; stressEnergyFromState =
        λ state →
          record
            { energyDensity =
                OldMDL.Lyapunov.L lyap state
            ; pressureX =
                OldMDL.Lyapunov.L lyap state
            ; pressureY =
                OldMDL.Lyapunov.L lyap state
            ; pressureZ =
                OldMDL.Lyapunov.L lyap state
            }
    ; energyDensityFromState =
        OldMDL.Lyapunov.L lyap
    ; isotropicPressureProxy =
        OldMDL.Lyapunov.L lyap
    ; stressEnergyDiagonal =
        λ state →
          record
            { energyDensity =
                OldMDL.Lyapunov.L lyap state
            ; pressureX =
                OldMDL.Lyapunov.L lyap state
            ; pressureY =
                OldMDL.Lyapunov.L lyap state
            ; pressureZ =
                OldMDL.Lyapunov.L lyap state
            }
    ; lyapunovEnergyMatchesDensity =
        λ _ → refl
    ; energyDensityDescent =
        OldMDL.Lyapunov.descent lyap
    ; interfaceBoundary =
        "Internal energyDensity is OldMDL.Lyapunov.L from MDLLyapunovShiftInstance.lyapunovShift"
        ∷ "Internal stressEnergyDiagonal is diag(rho,p,p,p) over Nat-valued proxies"
        ∷ "The current typed pressure proxy is p = rho; the proposed p = J/3 needs a separate Nat/rational division adapter"
        ∷ "The available law is Lyapunov descent L(step state) <= L state, not exact conservation"
        ∷ "No Candidate256 physical calibration, W4 matter authority, Einstein equation law, or GR/QFT promotion is constructed"
        ∷ []
    }

canonicalInternalMDLStressEnergyBridgeReceipt :
  InternalMDLStressEnergyBridgeReceipt
canonicalInternalMDLStressEnergyBridgeReceipt =
  record
    { m =
        1
    ; k =
        3
    ; internalInterface =
        internalShiftMDLStressEnergyInterface 1 3
    ; sourceLyapunovName =
        "DASHI.Physics.Closure.MDLLyapunovShiftInstance.lyapunovShift"
    ; sourceStateName =
        "DASHI.Physics.RealTernaryCarrier.Carrier (m + k)"
    ; proposedAdapterStatus =
        "energyDensity = OldMDL.Lyapunov.L lyapunovShift is inhabited"
        ∷ "stress-energy-shaped internal diagonal diag(rho,p,p,p) is inhabited over Nat proxies"
        ∷ "isotropic pressure p = J/3 is adapter-needed: no physical/rational pressure carrier is supplied by the current W4 interface"
        ∷ "conservation from MDL Lyapunov descent is obstructed: the available theorem is <= descent, not equality or divergence-free conservation"
        ∷ []
    ; adapterObstruction =
        canonicalW4MatterStressEnergyAdapterObstruction
    ; exactObstructionToW4Promotion =
        "W4MatterStressEnergyPromotion still requires Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "W4MatterStressEnergyInterfaceReceipt still requires W4 authority-backed matter and stress-energy fields"
        ∷ "EinsteinEquationCandidate still gates sourced non-flat GR on W4 matter coupling"
        ∷ "This internal bridge has no accepted physical units, no calibration map, and no Einstein-law consumer"
        ∷ []
    ; noW4Promotion =
        W4SE.w4MatterStressEnergyPromotionImpossibleHere
    }
