module DASHI.Physics.Closure.NSCarrierEnergyInequalityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ParaproductDecompositionReceipt as Para

data NSCarrierEnergyInput : Set where
  finiteDepthL2Energy :
    NSCarrierEnergyInput

  primeBandBernsteinControl :
    NSCarrierEnergyInput

  paraproductCancellationBookkeeping :
    NSCarrierEnergyInput

canonicalNSCarrierEnergyInputs :
  List NSCarrierEnergyInput
canonicalNSCarrierEnergyInputs =
  finiteDepthL2Energy
  ∷ primeBandBernsteinControl
  ∷ paraproductCancellationBookkeeping
  ∷ []

nsCarrierEnergyInequalityStatement : String
nsCarrierEnergyInequalityStatement =
  "The prime-band NS carrier tranche records the Leray energy inequality with paraproduct cancellation bookkeeping; this is weak-solution scoped."

record NSCarrierEnergyInequalityReceipt : Setω where
  field
    paraproductReceipt :
      Para.ParaproductDecompositionReceipt

    paraproductCancellationInputRecorded :
      Para.resonantTermBoundedByH34 paraproductReceipt ≡ true

    inputs :
      List NSCarrierEnergyInput

    inputsAreCanonical :
      inputs ≡ canonicalNSCarrierEnergyInputs

    nonlinearCancellationRecorded :
      Bool

    nonlinearCancellationRecordedIsTrue :
      nonlinearCancellationRecorded ≡ true

    carrierL2EnergyInequalityRecorded :
      Bool

    carrierL2EnergyInequalityRecordedIsTrue :
      carrierL2EnergyInequalityRecorded ≡ true

    lerayEnergyInequalityScoped :
      Bool

    lerayEnergyInequalityScopedIsTrue :
      lerayEnergyInequalityScoped ≡ true

    energyEqualityPromoted :
      Bool

    energyEqualityPromotedIsFalse :
      energyEqualityPromoted ≡ false

    smoothRegularityFromEnergy :
      Bool

    smoothRegularityFromEnergyIsFalse :
      smoothRegularityFromEnergy ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCarrierEnergyInequalityStatement

    receiptBoundary :
      List String

open NSCarrierEnergyInequalityReceipt public

canonicalNSCarrierEnergyInequalityReceipt :
  NSCarrierEnergyInequalityReceipt
canonicalNSCarrierEnergyInequalityReceipt =
  record
    { paraproductReceipt =
        Para.canonicalParaproductDecompositionReceipt
    ; paraproductCancellationInputRecorded =
        refl
    ; inputs =
        canonicalNSCarrierEnergyInputs
    ; inputsAreCanonical =
        refl
    ; nonlinearCancellationRecorded =
        true
    ; nonlinearCancellationRecordedIsTrue =
        refl
    ; carrierL2EnergyInequalityRecorded =
        true
    ; carrierL2EnergyInequalityRecordedIsTrue =
        refl
    ; lerayEnergyInequalityScoped =
        true
    ; lerayEnergyInequalityScopedIsTrue =
        refl
    ; energyEqualityPromoted =
        false
    ; energyEqualityPromotedIsFalse =
        refl
    ; smoothRegularityFromEnergy =
        false
    ; smoothRegularityFromEnergyIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsCarrierEnergyInequalityStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The recorded inequality is the Leray energy inequality, not energy equality"
        ∷ "Paraproduct cancellation is used only for weak-solution energy bookkeeping"
        ∷ "Smooth regularity and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

nsCarrierEnergyInequalityKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSCarrierEnergyInequalityReceipt ≡ false
nsCarrierEnergyInequalityKeepsClayFalse =
  refl
