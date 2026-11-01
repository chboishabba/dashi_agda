module DASHI.Physics.Closure.NSCarrierContinuumLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.UltrametricAubinLionsCompactness as Compact

data NSContinuumLimitInput : Set where
  aubinLionsStrongL2Convergence : NSContinuumLimitInput
  ladyzhenskayaL4Interpolation : NSContinuumLimitInput
  lerayGradientBound : NSContinuumLimitInput
  distributionalWeakForm : NSContinuumLimitInput

canonicalNSContinuumLimitInputs :
  List NSContinuumLimitInput
canonicalNSContinuumLimitInputs =
  aubinLionsStrongL2Convergence
  ∷ ladyzhenskayaL4Interpolation
  ∷ lerayGradientBound
  ∷ distributionalWeakForm
  ∷ []

data NSContinuumLimitBlocker : Set where
  missingCarrierSpecializedAubinLions : NSContinuumLimitBlocker
  missingStrongL2ConvergenceHypothesis : NSContinuumLimitBlocker
  missingContinuumBKMRegularityPassage : NSContinuumLimitBlocker

canonicalNSContinuumLimitBlockers :
  List NSContinuumLimitBlocker
canonicalNSContinuumLimitBlockers =
  missingCarrierSpecializedAubinLions
  ∷ missingStrongL2ConvergenceHypothesis
  ∷ missingContinuumBKMRegularityPassage
  ∷ []

nsNonlinearPassageStatement : String
nsNonlinearPassageStatement =
  "Conditional target: strong L2 convergence plus Ladyzhenskaya and Leray bounds imply (u_d dot grad)u_d -> (u_inf dot grad)u_inf distributionally."

record NSCarrierContinuumLimitReceipt : Setω where
  field
    compactnessReceipt :
      Compact.UltrametricAubinLionsCompactnessReceipt

    carrierSpecializedCompactnessStillOpen :
      Compact.carrierSpecializedCompactnessConstructed compactnessReceipt
      ≡
      false

    inputs :
      List NSContinuumLimitInput

    inputsAreCanonical :
      inputs ≡ canonicalNSContinuumLimitInputs

    nonlinearTermConvergenceRouteRecorded :
      Bool

    nonlinearTermConvergenceRouteRecordedIsTrue :
      nonlinearTermConvergenceRouteRecorded ≡ true

    nsNonlinearTermConvergesConditional :
      Bool

    nsNonlinearTermConvergesConditionalIsTrue :
      nsNonlinearTermConvergesConditional ≡ true

    nsWeakSolutionLimitInhabitedUnconditionally :
      Bool

    nsWeakSolutionLimitInhabitedUnconditionallyIsFalse :
      nsWeakSolutionLimitInhabitedUnconditionally ≡ false

    nsSmoothContinuumLimit :
      Bool

    nsSmoothContinuumLimitIsFalse :
      nsSmoothContinuumLimit ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    nonlinearPassageStatement :
      String

    nonlinearPassageStatementIsCanonical :
      nonlinearPassageStatement ≡ nsNonlinearPassageStatement

    blockers :
      List NSContinuumLimitBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSContinuumLimitBlockers

    receiptBoundary :
      List String

open NSCarrierContinuumLimitReceipt public

canonicalNSCarrierContinuumLimitReceipt :
  NSCarrierContinuumLimitReceipt
canonicalNSCarrierContinuumLimitReceipt =
  record
    { compactnessReceipt =
        Compact.canonicalUltrametricAubinLionsCompactnessReceipt
    ; carrierSpecializedCompactnessStillOpen =
        refl
    ; inputs =
        canonicalNSContinuumLimitInputs
    ; inputsAreCanonical =
        refl
    ; nonlinearTermConvergenceRouteRecorded =
        true
    ; nonlinearTermConvergenceRouteRecordedIsTrue =
        refl
    ; nsNonlinearTermConvergesConditional =
        true
    ; nsNonlinearTermConvergesConditionalIsTrue =
        refl
    ; nsWeakSolutionLimitInhabitedUnconditionally =
        false
    ; nsWeakSolutionLimitInhabitedUnconditionallyIsFalse =
        refl
    ; nsSmoothContinuumLimit =
        false
    ; nsSmoothContinuumLimitIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; nonlinearPassageStatement =
        nsNonlinearPassageStatement
    ; nonlinearPassageStatementIsCanonical =
        refl
    ; blockers =
        canonicalNSContinuumLimitBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The nonlinear-term passage is recorded as conditional on carrier-specialized Aubin-Lions strong L2 convergence"
        ∷ "No unconditional weak continuum NS solution is promoted here"
        ∷ "Smooth continuum regularity, BKM passage, and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

nsCarrierContinuumLimitDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCarrierContinuumLimitReceipt
  ≡
  false
nsCarrierContinuumLimitDoesNotPromoteClay =
  refl
