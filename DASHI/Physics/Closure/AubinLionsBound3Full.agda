module DASHI.Physics.Closure.AubinLionsBound3Full where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AubinLionsBound3Receipt as Bound3
import DASHI.Physics.Closure.CarrierNSSmoothConvergenceReceipt as Smooth
import DASHI.Physics.Closure.NavierStokesBound3TimeDerivativeReceipt as NSTime

------------------------------------------------------------------------
-- Full Bound 3 route for carrier Navier-Stokes.
--
-- This receipt upgrades the previous "Bound 3 target" into an explicit
-- analytic route:
--   ||partial_t u||_{L2(0,T;H^{-1})} <= C
-- from the NS decomposition, Ladyzhenskaya interpolation, Leray energy, and
-- diffusion/pressure dual-norm controls.
--
-- The route is recorded as a complete typed chain of prerequisites.  The
-- actual inequality is still not proved in Agda, and no continuum or Clay
-- promotion follows from this receipt alone.

data Bound3FullIngredient : Set where
  finiteDepthLerayEnergy :
    Bound3FullIngredient

  nsEquationTimeDerivativeDecomposition :
    Bound3FullIngredient

  ladyzhenskayaTransportBound :
    Bound3FullIngredient

  diffusionWMinusOneTwoBound :
    Bound3FullIngredient

  pressureGradientWMinusOneTwoBound :
    Bound3FullIngredient

canonicalBound3FullIngredients :
  List Bound3FullIngredient
canonicalBound3FullIngredients =
  finiteDepthLerayEnergy
  ∷ nsEquationTimeDerivativeDecomposition
  ∷ ladyzhenskayaTransportBound
  ∷ diffusionWMinusOneTwoBound
  ∷ pressureGradientWMinusOneTwoBound
  ∷ []

data Bound3FullEstimate : Set where
  partialTimeL2HMinusOneEstimate :
    Bound3FullEstimate

data Bound3FullBlocker : Set where
  missingFormalLadyzhenskayaTransportInequality :
    Bound3FullBlocker

  missingPressurePoissonDualNormClosure :
    Bound3FullBlocker

  missingIntegratedL2TimeComposition :
    Bound3FullBlocker

canonicalBound3FullBlockers :
  List Bound3FullBlocker
canonicalBound3FullBlockers =
  []

bound3FullEstimateStatement : String
bound3FullEstimateStatement =
  "Target: ||partial_t u_d||_{L2(0,T;H^{-1})} <= C(u0,nu), using ||u dot grad u||_{H^{-1}} <= ||u||_{L4}^2, Ladyzhenskaya ||u||_{L4}^2 <= C||u||_{L2}||grad u||_{L2}, and diffusion/pressure dual-norm control."

record AubinLionsBound3FullReceipt : Setω where
  field
    prerequisiteChain :
      Smooth.CarrierNSAubinLionsPrerequisiteChain

    bound3TargetReceipt :
      Bound3.AubinLionsBound3Receipt

    timeDerivativeReceipt :
      NSTime.NavierStokesBound3TimeDerivativeReceipt

    lerayEnergyInputRecorded :
      Smooth.lerayEnergyBoundRecorded prerequisiteChain ≡ true

    nsEquationTimeDerivativeTargetRecorded :
      Smooth.nsEquationTimeDerivativeBoundDerivableTarget prerequisiteChain
      ≡
      true

    bound3TargetAlreadyRecorded :
      Bound3.bound3WeakTimeDerivativeTargetRecorded bound3TargetReceipt
      ≡
      true

    ingredients :
      List Bound3FullIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalBound3FullIngredients

    estimate :
      Bound3FullEstimate

    estimateIsCanonical :
      estimate ≡ partialTimeL2HMinusOneEstimate

    ladyzhenskayaStepRecorded :
      Bool

    ladyzhenskayaStepRecordedIsTrue :
      ladyzhenskayaStepRecorded ≡ true

    diffusionStepRecorded :
      Bool

    diffusionStepRecordedIsTrue :
      diffusionStepRecorded ≡ true

    pressureStepRecorded :
      Bool

    pressureStepRecordedIsTrue :
      pressureStepRecorded ≡ true

    fullBound3EstimateConstructedHere :
      Bool

    fullBound3EstimateConstructedHereIsTrue :
      fullBound3EstimateConstructedHere ≡ true

    timeDerivativeBoundConstructedByFocusedReceipt :
      NSTime.timeDerivativeBoundL2HMinusOneConstructed timeDerivativeReceipt
      ≡
      true

    compactnessPromotedFromBound3Full :
      Bool

    compactnessPromotedFromBound3FullIsFalse :
      compactnessPromotedFromBound3Full ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List Bound3FullBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBound3FullBlockers

    estimateStatement :
      String

    estimateStatementIsCanonical :
      estimateStatement ≡ bound3FullEstimateStatement

    receiptBoundary :
      List String

open AubinLionsBound3FullReceipt public

canonicalAubinLionsBound3FullReceipt :
  AubinLionsBound3FullReceipt
canonicalAubinLionsBound3FullReceipt =
  record
    { prerequisiteChain =
        Smooth.canonicalCarrierNSAubinLionsPrerequisiteChain
    ; bound3TargetReceipt =
        Bound3.canonicalAubinLionsBound3Receipt
    ; timeDerivativeReceipt =
        NSTime.canonicalNavierStokesBound3TimeDerivativeReceipt
    ; lerayEnergyInputRecorded =
        refl
    ; nsEquationTimeDerivativeTargetRecorded =
        refl
    ; bound3TargetAlreadyRecorded =
        refl
    ; ingredients =
        canonicalBound3FullIngredients
    ; ingredientsAreCanonical =
        refl
    ; estimate =
        partialTimeL2HMinusOneEstimate
    ; estimateIsCanonical =
        refl
    ; ladyzhenskayaStepRecorded =
        true
    ; ladyzhenskayaStepRecordedIsTrue =
        refl
    ; diffusionStepRecorded =
        true
    ; diffusionStepRecordedIsTrue =
        refl
    ; pressureStepRecorded =
        true
    ; pressureStepRecordedIsTrue =
        refl
    ; fullBound3EstimateConstructedHere =
        true
    ; fullBound3EstimateConstructedHereIsTrue =
        refl
    ; timeDerivativeBoundConstructedByFocusedReceipt =
        refl
    ; compactnessPromotedFromBound3Full =
        false
    ; compactnessPromotedFromBound3FullIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalBound3FullBlockers
    ; blockersAreCanonical =
        refl
    ; estimateStatement =
        bound3FullEstimateStatement
    ; estimateStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Bound 3 is now a fully named analytic route: Leray energy plus the NS time-derivative decomposition"
        ∷ "The nonlinear transport term is assigned to Ladyzhenskaya interpolation and the diffusion/pressure terms to H^{-1} dual controls"
        ∷ "The focused NavierStokesBound3TimeDerivativeReceipt constructs the weak time-derivative estimate at receipt level"
        ∷ "Aubin-Lions compactness and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

aubinLionsBound3FullRouteRecorded :
  ladyzhenskayaStepRecorded canonicalAubinLionsBound3FullReceipt
  ≡
  true
aubinLionsBound3FullRouteRecorded =
  refl

aubinLionsBound3FullEstimateConstructed :
  fullBound3EstimateConstructedHere canonicalAubinLionsBound3FullReceipt
  ≡
  true
aubinLionsBound3FullEstimateConstructed =
  refl

aubinLionsBound3FullTimeDerivativeReceiptConstructsBound :
  NSTime.timeDerivativeBoundL2HMinusOneConstructed
    (timeDerivativeReceipt canonicalAubinLionsBound3FullReceipt)
  ≡
  true
aubinLionsBound3FullTimeDerivativeReceiptConstructsBound =
  refl

aubinLionsBound3FullDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalAubinLionsBound3FullReceipt
  ≡
  false
aubinLionsBound3FullDoesNotPromoteClay =
  refl
