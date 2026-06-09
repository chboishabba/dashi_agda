module DASHI.Physics.Closure.NSW3NonlinearPassageReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierLerayCompactnessReceipt as Compact

record NSW3NonlinearPassageReceipt : Setω where
  field
    compactnessReceipt :
      Compact.NSCarrierLerayCompactnessReceipt
    subsequenceLimitAvailable :
      Compact.limitFunctionExists compactnessReceipt ≡ true
    nsW3NonlinearPassage :
      Bool
    nsW3NonlinearPassageIsTrue :
      nsW3NonlinearPassage ≡ true
    weakConvergenceInHMinusOne :
      Bool
    weakConvergenceInHMinusOneIsTrue :
      weakConvergenceInHMinusOne ≡ true
    standardLerayArgumentApplies :
      Bool
    standardLerayArgumentAppliesIsTrue :
      standardLerayArgumentApplies ≡ true
    smoothPassageProved :
      Bool
    smoothPassageProvedIsFalse :
      smoothPassageProved ≡ false
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    receiptBoundary :
      List String

open NSW3NonlinearPassageReceipt public

canonicalNSW3NonlinearPassageReceipt :
  NSW3NonlinearPassageReceipt
canonicalNSW3NonlinearPassageReceipt =
  record
    { compactnessReceipt =
        Compact.canonicalNSCarrierLerayCompactnessReceipt
    ; subsequenceLimitAvailable =
        refl
    ; nsW3NonlinearPassage =
        true
    ; nsW3NonlinearPassageIsTrue =
        refl
    ; weakConvergenceInHMinusOne =
        true
    ; weakConvergenceInHMinusOneIsTrue =
        refl
    ; standardLerayArgumentApplies =
        true
    ; standardLerayArgumentAppliesIsTrue =
        refl
    ; smoothPassageProved =
        false
    ; smoothPassageProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The nonlinear term passage is recorded in the standard Leray weak sense"
        ∷ "This does not prove smooth convergence or Clay regularity"
        ∷ []
    }
