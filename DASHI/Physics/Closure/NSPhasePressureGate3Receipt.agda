module DASHI.Physics.Closure.NSPhasePressureGate3Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes Gate 3 phase/pressure obstruction receipt.
--
-- This receipt records the corrected Gate 3 boundary for the NS carrier
-- programme.  Gate 3 now has two obstructions: local phase loss and global
-- pressure non-locality.  The phase obstruction is addressable by extending
-- the atom phase/unit-group dictionary.  The pressure obstruction is not
-- recoverable from a finite local atom dictionary without global coupling or
-- an explicit pressure field, because pressure is obtained through the
-- elliptic solve Δp = -tr((∇u)^2).  No carrier-to-general NS theorem and no
-- Clay promotion are made here.

data NSPhasePressureGate3Status : Set where
  gate3HasPhaseLossAndPressureNonlocality_noClayPromotion :
    NSPhasePressureGate3Status

data NSGate3Obstruction : Set where
  phaseLossLocalAddressableByAtomPhaseUnitGroupExtension :
    NSGate3Obstruction

  pressureNonlocalityGlobalEllipticSolve :
    NSGate3Obstruction

canonicalNSGate3Obstructions :
  List NSGate3Obstruction
canonicalNSGate3Obstructions =
  phaseLossLocalAddressableByAtomPhaseUnitGroupExtension
  ∷ pressureNonlocalityGlobalEllipticSolve
  ∷ []

data NSGate3Observable : Set where
  atomPhase :
    NSGate3Observable

  unitGroupPhase :
    NSGate3Observable

  localVelocityGradient :
    NSGate3Observable

  pressureGradient :
    NSGate3Observable

canonicalNSGate3RequiredObservables :
  List NSGate3Observable
canonicalNSGate3RequiredObservables =
  atomPhase
  ∷ unitGroupPhase
  ∷ localVelocityGradient
  ∷ pressureGradient
  ∷ []

data NSPressureRecoveryBoundary : Set where
  finiteLocalAtomDictionaryInsufficient :
    NSPressureRecoveryBoundary

  globalCouplingOrPressureFieldRequired :
    NSPressureRecoveryBoundary

canonicalNSPressureRecoveryBoundary :
  List NSPressureRecoveryBoundary
canonicalNSPressureRecoveryBoundary =
  finiteLocalAtomDictionaryInsufficient
  ∷ globalCouplingOrPressureFieldRequired
  ∷ []

data NSGate3OpenBridge : Set where
  carrierToGeneralNavierStokesStillOpen :
    NSGate3OpenBridge

canonicalNSGate3OpenBridges :
  List NSGate3OpenBridge
canonicalNSGate3OpenBridges =
  carrierToGeneralNavierStokesStillOpen
  ∷ []

data NSPhasePressureGate3Promotion : Set where

nsPhasePressureGate3PromotionImpossibleHere :
  NSPhasePressureGate3Promotion →
  ⊥
nsPhasePressureGate3PromotionImpossibleHere ()

nsPhasePressureGate3Statement :
  String
nsPhasePressureGate3Statement =
  "NS Gate 3 has two obstructions: phase loss is local and addressable by atom phase/unit-group extension; pressure non-locality is global, governed by Δp = -tr((∇u)^2), and requires coupling or a pressure field."

nsPressureGradientStatement :
  String
nsPressureGradientStatement =
  "pressureGradient is a required global-coupling observable for NS Gate 3; it is not recovered from a finite local atom dictionary alone."

nsNoClayPromotionStatement :
  String
nsNoClayPromotionStatement =
  "Carrier-to-general Navier-Stokes remains open and Clay Navier-Stokes is not promoted by this receipt."

record NSPhasePressureGate3Receipt : Setω where
  field
    status :
      NSPhasePressureGate3Status

    statusIsCanonical :
      status
      ≡
      gate3HasPhaseLossAndPressureNonlocality_noClayPromotion

    obstructions :
      List NSGate3Obstruction

    obstructionsAreCanonical :
      obstructions ≡ canonicalNSGate3Obstructions

    phaseLossRecorded :
      Bool

    phaseLossRecordedIsTrue :
      phaseLossRecorded ≡ true

    phaseLossIsLocal :
      Bool

    phaseLossIsLocalIsTrue :
      phaseLossIsLocal ≡ true

    phaseLossAddressableByAtomPhaseUnitGroupExtension :
      Bool

    phaseLossAddressableByAtomPhaseUnitGroupExtensionIsTrue :
      phaseLossAddressableByAtomPhaseUnitGroupExtension ≡ true

    pressureNonlocalityRecorded :
      Bool

    pressureNonlocalityRecordedIsTrue :
      pressureNonlocalityRecorded ≡ true

    pressureNonlocalityIsGlobal :
      Bool

    pressureNonlocalityIsGlobalIsTrue :
      pressureNonlocalityIsGlobal ≡ true

    pressureEllipticSolveRecorded :
      Bool

    pressureEllipticSolveRecordedIsTrue :
      pressureEllipticSolveRecorded ≡ true

    pressureEquation :
      String

    pressureEquationIsCanonical :
      pressureEquation ≡ "Δp = -tr((∇u)^2)"

    requiredObservables :
      List NSGate3Observable

    requiredObservablesAreCanonical :
      requiredObservables ≡ canonicalNSGate3RequiredObservables

    pressureGradientRequired :
      Bool

    pressureGradientRequiredIsTrue :
      pressureGradientRequired ≡ true

    pressureGradientIsGlobalCouplingObservable :
      Bool

    pressureGradientIsGlobalCouplingObservableIsTrue :
      pressureGradientIsGlobalCouplingObservable ≡ true

    finiteLocalAtomDictionaryRecoversPressure :
      Bool

    finiteLocalAtomDictionaryRecoversPressureIsFalse :
      finiteLocalAtomDictionaryRecoversPressure ≡ false

    pressureRecoverableWithoutCouplingOrPressureField :
      Bool

    pressureRecoverableWithoutCouplingOrPressureFieldIsFalse :
      pressureRecoverableWithoutCouplingOrPressureField ≡ false

    pressureRecoveryBoundary :
      List NSPressureRecoveryBoundary

    pressureRecoveryBoundaryIsCanonical :
      pressureRecoveryBoundary ≡ canonicalNSPressureRecoveryBoundary

    openBridges :
      List NSGate3OpenBridge

    openBridgesAreCanonical :
      openBridges ≡ canonicalNSGate3OpenBridges

    carrierToGeneralNavierStokesOpen :
      Bool

    carrierToGeneralNavierStokesOpenIsTrue :
      carrierToGeneralNavierStokesOpen ≡ true

    carrierToGeneralNavierStokesPromoted :
      Bool

    carrierToGeneralNavierStokesPromotedIsFalse :
      carrierToGeneralNavierStokesPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsPhasePressureGate3Statement

    pressureGradientBoundary :
      String

    pressureGradientBoundaryIsCanonical :
      pressureGradientBoundary ≡ nsPressureGradientStatement

    noClayPromotionBoundary :
      String

    noClayPromotionBoundaryIsCanonical :
      noClayPromotionBoundary ≡ nsNoClayPromotionStatement

    promotionFlags :
      List NSPhasePressureGate3Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSPhasePressureGate3Receipt public

canonicalNSPhasePressureGate3Receipt :
  NSPhasePressureGate3Receipt
canonicalNSPhasePressureGate3Receipt =
  record
    { status =
        gate3HasPhaseLossAndPressureNonlocality_noClayPromotion
    ; statusIsCanonical =
        refl
    ; obstructions =
        canonicalNSGate3Obstructions
    ; obstructionsAreCanonical =
        refl
    ; phaseLossRecorded =
        true
    ; phaseLossRecordedIsTrue =
        refl
    ; phaseLossIsLocal =
        true
    ; phaseLossIsLocalIsTrue =
        refl
    ; phaseLossAddressableByAtomPhaseUnitGroupExtension =
        true
    ; phaseLossAddressableByAtomPhaseUnitGroupExtensionIsTrue =
        refl
    ; pressureNonlocalityRecorded =
        true
    ; pressureNonlocalityRecordedIsTrue =
        refl
    ; pressureNonlocalityIsGlobal =
        true
    ; pressureNonlocalityIsGlobalIsTrue =
        refl
    ; pressureEllipticSolveRecorded =
        true
    ; pressureEllipticSolveRecordedIsTrue =
        refl
    ; pressureEquation =
        "Δp = -tr((∇u)^2)"
    ; pressureEquationIsCanonical =
        refl
    ; requiredObservables =
        canonicalNSGate3RequiredObservables
    ; requiredObservablesAreCanonical =
        refl
    ; pressureGradientRequired =
        true
    ; pressureGradientRequiredIsTrue =
        refl
    ; pressureGradientIsGlobalCouplingObservable =
        true
    ; pressureGradientIsGlobalCouplingObservableIsTrue =
        refl
    ; finiteLocalAtomDictionaryRecoversPressure =
        false
    ; finiteLocalAtomDictionaryRecoversPressureIsFalse =
        refl
    ; pressureRecoverableWithoutCouplingOrPressureField =
        false
    ; pressureRecoverableWithoutCouplingOrPressureFieldIsFalse =
        refl
    ; pressureRecoveryBoundary =
        canonicalNSPressureRecoveryBoundary
    ; pressureRecoveryBoundaryIsCanonical =
        refl
    ; openBridges =
        canonicalNSGate3OpenBridges
    ; openBridgesAreCanonical =
        refl
    ; carrierToGeneralNavierStokesOpen =
        true
    ; carrierToGeneralNavierStokesOpenIsTrue =
        refl
    ; carrierToGeneralNavierStokesPromoted =
        false
    ; carrierToGeneralNavierStokesPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsPhasePressureGate3Statement
    ; statementIsCanonical =
        refl
    ; pressureGradientBoundary =
        nsPressureGradientStatement
    ; pressureGradientBoundaryIsCanonical =
        refl
    ; noClayPromotionBoundary =
        nsNoClayPromotionStatement
    ; noClayPromotionBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Gate 3 now records both local phase loss and global pressure non-locality"
        ∷ "Phase loss is local and addressable by atom phase/unit-group extension"
        ∷ "Pressure is governed by the global elliptic solve Δp = -tr((∇u)^2)"
        ∷ "pressureGradient is required as a global-coupling observable"
        ∷ "A finite local atom dictionary alone does not recover pressure without coupling or a pressure field"
        ∷ "Carrier-to-general NS remains open and Clay Navier-Stokes is not promoted"
        ∷ []
    }

nsGate3PressureGradientRequired :
  pressureGradientRequired canonicalNSPhasePressureGate3Receipt ≡ true
nsGate3PressureGradientRequired =
  refl

nsGate3FiniteLocalAtomDictionaryDoesNotRecoverPressure :
  finiteLocalAtomDictionaryRecoversPressure
    canonicalNSPhasePressureGate3Receipt
  ≡
  false
nsGate3FiniteLocalAtomDictionaryDoesNotRecoverPressure =
  refl

nsGate3CarrierToGeneralStillOpen :
  carrierToGeneralNavierStokesOpen canonicalNSPhasePressureGate3Receipt
  ≡
  true
nsGate3CarrierToGeneralStillOpen =
  refl

nsGate3KeepsClayFalse :
  clayNavierStokesPromoted canonicalNSPhasePressureGate3Receipt ≡ false
nsGate3KeepsClayFalse =
  refl
