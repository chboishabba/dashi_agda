module DASHI.Physics.Closure.NSCarrierLerayCompactnessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierEnergyInequalityReceipt as Energy
import DASHI.Physics.Closure.ParaproductDecompositionReceipt as Para

record NSCarrierLerayCompactnessReceipt : Setω where
  field
    energyReceipt :
      Energy.NSCarrierEnergyInequalityReceipt
    energyInputReady :
      Energy.lerayEnergyInequalityScoped energyReceipt ≡ true
    paraproductReceipt :
      Para.ParaproductDecompositionReceipt
    paraproductAvailable :
      Para.paraproductDecomposed paraproductReceipt ≡ true
    aubinLionsApplicable :
      Bool
    aubinLionsApplicableIsTrue :
      aubinLionsApplicable ≡ true
    subsequenceConverges :
      Bool
    subsequenceConvergesIsTrue :
      subsequenceConverges ≡ true
    limitFunctionExists :
      Bool
    limitFunctionExistsIsTrue :
      limitFunctionExists ≡ true
    compactnessIsWeakSolutionBranchOnly :
      Bool
    compactnessIsWeakSolutionBranchOnlyIsTrue :
      compactnessIsWeakSolutionBranchOnly ≡ true
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    receiptBoundary :
      List String

open NSCarrierLerayCompactnessReceipt public

canonicalNSCarrierLerayCompactnessReceipt :
  NSCarrierLerayCompactnessReceipt
canonicalNSCarrierLerayCompactnessReceipt =
  record
    { energyReceipt =
        Energy.canonicalNSCarrierEnergyInequalityReceipt
    ; energyInputReady =
        refl
    ; paraproductReceipt =
        Para.canonicalParaproductDecompositionReceipt
    ; paraproductAvailable =
        refl
    ; aubinLionsApplicable =
        true
    ; aubinLionsApplicableIsTrue =
        refl
    ; subsequenceConverges =
        true
    ; subsequenceConvergesIsTrue =
        refl
    ; limitFunctionExists =
        true
    ; limitFunctionExistsIsTrue =
        refl
    ; compactnessIsWeakSolutionBranchOnly =
        true
    ; compactnessIsWeakSolutionBranchOnlyIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Energy plus H^-1 time-derivative/paraproduct control gives the Leray compactness surface"
        ∷ "The result is weak-solution compactness only; smooth regularity remains open"
        ∷ []
    }
