module DASHI.Physics.Closure.UltrametricAubinLionsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierNSSmoothConvergenceReceipt as Smooth
import DASHI.Physics.Closure.AubinLionsBound3Receipt as Bound3

------------------------------------------------------------------------
-- Ultrametric Aubin-Lions frontier.
--
-- This receipt packages the three-bound Aubin-Lions route for Navier-Stokes:
-- Leray energy, ultrametric Sobolev uniformity, and a weak time-derivative
-- bound.  The first two are already recorded by existing receipts; the third
-- is recorded as derivable target.  Compactness, smooth limit construction,
-- and Clay promotion remain false.

data UltrametricAubinLionsBound : Set where
  lerayEnergyBound :
    UltrametricAubinLionsBound

  ultrametricSobolevUniformBound :
    UltrametricAubinLionsBound

  weakTimeDerivativeBound :
    UltrametricAubinLionsBound

data Bound3WeakTimeDerivativeRouteComponent : Set where
  ladyzhenskayaInterpolationComponent :
    Bound3WeakTimeDerivativeRouteComponent

  diffusionDualNormComponent :
    Bound3WeakTimeDerivativeRouteComponent

  pressureGradientTargetComponent :
    Bound3WeakTimeDerivativeRouteComponent

data LadyzhenskayaInterpolationTarget : Set where
  ladyzhenskayaL4FromL2H1Target :
    LadyzhenskayaInterpolationTarget

data DiffusionDualNormTarget : Set where
  diffusionTermControlledInWMinusOneTwoTarget :
    DiffusionDualNormTarget

data PressureGradientDualTarget : Set where
  pressureGradientControlledInWMinusOneTwoTarget :
    PressureGradientDualTarget

data Bound3WeakTimeDerivativeEstimateTarget : Set where
  bound3PartialTimeEstimateFromNSDecomposition :
    LadyzhenskayaInterpolationTarget →
    DiffusionDualNormTarget →
    PressureGradientDualTarget →
    Bound3WeakTimeDerivativeEstimateTarget

data UltrametricAubinLionsBlocker : Set where
  missingCarrierSpecializedAubinLionsLemma :
    UltrametricAubinLionsBlocker

  missingFormalWeakTimeDerivativeEstimate :
    UltrametricAubinLionsBlocker

  missingFormalBound3CompositionOfTargets :
    UltrametricAubinLionsBlocker

  missingPrecompactnessToCinftyBootstrap :
    UltrametricAubinLionsBlocker

  missingContinuumNSEquationPreservation :
    UltrametricAubinLionsBlocker

  missingBKMContinuumPassage :
    UltrametricAubinLionsBlocker

canonicalUltrametricAubinLionsBounds :
  List UltrametricAubinLionsBound
canonicalUltrametricAubinLionsBounds =
  lerayEnergyBound
  ∷ ultrametricSobolevUniformBound
  ∷ weakTimeDerivativeBound
  ∷ []

canonicalBound3WeakTimeDerivativeRouteComponents :
  List Bound3WeakTimeDerivativeRouteComponent
canonicalBound3WeakTimeDerivativeRouteComponents =
  ladyzhenskayaInterpolationComponent
  ∷ diffusionDualNormComponent
  ∷ pressureGradientTargetComponent
  ∷ []

canonicalUltrametricAubinLionsBlockers :
  List UltrametricAubinLionsBlocker
canonicalUltrametricAubinLionsBlockers =
  missingCarrierSpecializedAubinLionsLemma
  ∷ missingFormalWeakTimeDerivativeEstimate
  ∷ missingFormalBound3CompositionOfTargets
  ∷ missingPrecompactnessToCinftyBootstrap
  ∷ missingContinuumNSEquationPreservation
  ∷ missingBKMContinuumPassage
  ∷ []

timeDerivativeEstimateStatement : String
timeDerivativeEstimateStatement =
  "partial_t u_d = -u_d dot grad u_d - grad p_d + nu Delta u_d; Leray energy plus Sobolev controls the W^{-1,2} norm as a derivable target"

bound3TimeDerivativeEstimateStatement : String
bound3TimeDerivativeEstimateStatement =
  "||partial_t u_d||_{L2(0,T;W^{-1,2})} <= C(u0,nu), by Ladyzhenskaya interpolation for the transport term, diffusion dual-norm control, and a pressure-gradient W^{-1,2} target"

record UltrametricAubinLionsReceipt : Setω where
  field
    smoothConvergenceReceipt :
      Smooth.CarrierNSSmoothConvergenceReceipt

    prerequisiteChain :
      Smooth.CarrierNSAubinLionsPrerequisiteChain

    bound3Receipt :
      Bound3.AubinLionsBound3Receipt

    lerayEnergyBoundAlreadyRecorded :
      Smooth.lerayEnergyBoundRecorded prerequisiteChain ≡ true

    ultrametricSobolevAlreadyRecorded :
      Smooth.ultrametricSobolevUniformityRecorded prerequisiteChain ≡ true

    timeDerivativeBoundRecordedAsTarget :
      Smooth.nsEquationTimeDerivativeBoundDerivableTarget prerequisiteChain
      ≡
      true

    timeDerivativeBoundConstructedHere :
      Bool

    timeDerivativeBoundConstructedHereIsFalse :
      timeDerivativeBoundConstructedHere ≡ false

    bound3LerayEnergyInputRecorded :
      Smooth.lerayEnergyBoundRecorded
        (Bound3.prerequisiteChain bound3Receipt)
      ≡
      true

    bound3LadyzhenskayaTargetRecorded :
      Bound3.ladyzhenskayaTargetRecorded bound3Receipt ≡ true

    bound3DiffusionDualNormTargetRecorded :
      Bound3.diffusionDualNormTargetRecorded bound3Receipt ≡ true

    bound3PressureGradientTargetRecorded :
      Bound3.pressureGradientTargetRecorded bound3Receipt ≡ true

    bound3FullProofDerivableFromCurrentLocalObjects :
      Bound3.fullBound3ProofDerivableFromCurrentLocalObjects bound3Receipt
      ≡
      false

    bound3CompactnessFlagStillFalse :
      Bound3.compactnessTheoremInstantiatedFromBound3 bound3Receipt
      ≡
      false

    bound3ClayFlagStillFalse :
      Bound3.clayNavierStokesPromotedFromBound3 bound3Receipt
      ≡
      false

    bound3RouteComponents :
      List Bound3WeakTimeDerivativeRouteComponent

    bound3RouteComponentsAreCanonical :
      bound3RouteComponents ≡ canonicalBound3WeakTimeDerivativeRouteComponents

    ladyzhenskayaInterpolationTarget :
      LadyzhenskayaInterpolationTarget

    ladyzhenskayaInterpolationTargetIsCanonical :
      ladyzhenskayaInterpolationTarget ≡ ladyzhenskayaL4FromL2H1Target

    diffusionDualNormTarget :
      DiffusionDualNormTarget

    diffusionDualNormTargetIsCanonical :
      diffusionDualNormTarget ≡ diffusionTermControlledInWMinusOneTwoTarget

    pressureGradientTarget :
      PressureGradientDualTarget

    pressureGradientTargetIsCanonical :
      pressureGradientTarget ≡ pressureGradientControlledInWMinusOneTwoTarget

    bound3WeakTimeDerivativeEstimateTarget :
      Bound3WeakTimeDerivativeEstimateTarget

    bound3WeakTimeDerivativeEstimateTargetIsCanonical :
      bound3WeakTimeDerivativeEstimateTarget
      ≡
      bound3PartialTimeEstimateFromNSDecomposition
        ladyzhenskayaInterpolationTarget
        diffusionDualNormTarget
        pressureGradientTarget

    bound3RouteRecorded :
      Bool

    bound3RouteRecordedIsTrue :
      bound3RouteRecorded ≡ true

    bound3EstimateRecordedAsResearchTarget :
      Bool

    bound3EstimateRecordedAsResearchTargetIsTrue :
      bound3EstimateRecordedAsResearchTarget ≡ true

    bound3EstimateConstructedHere :
      Bool

    bound3EstimateConstructedHereIsFalse :
      bound3EstimateConstructedHere ≡ false

    bounds :
      List UltrametricAubinLionsBound

    boundsAreCanonical :
      bounds ≡ canonicalUltrametricAubinLionsBounds

    compactnessTheoremInstantiated :
      Bool

    compactnessTheoremInstantiatedIsFalse :
      compactnessTheoremInstantiated ≡ false

    precompactnessConstructed :
      Bool

    precompactnessConstructedIsFalse :
      precompactnessConstructed ≡ false

    continuumLimitExistsConstructed :
      Bool

    continuumLimitExistsConstructedIsFalse :
      continuumLimitExistsConstructed ≡ false

    limitIsSmoothConstructed :
      Bool

    limitIsSmoothConstructedIsFalse :
      limitIsSmoothConstructed ≡ false

    limitSatisfiesContinuumNSConstructed :
      Bool

    limitSatisfiesContinuumNSConstructedIsFalse :
      limitSatisfiesContinuumNSConstructed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    existingSmoothConvergenceClayFlagStillFalse :
      Smooth.clayNSSmoothnessClosed smoothConvergenceReceipt
      ≡
      false

    blockers :
      List UltrametricAubinLionsBlocker

    blockersAreCanonical :
      blockers ≡ canonicalUltrametricAubinLionsBlockers

    timeDerivativeEstimate :
      String

    timeDerivativeEstimateIsCanonical :
      timeDerivativeEstimate ≡ timeDerivativeEstimateStatement

    bound3TimeDerivativeEstimate :
      String

    bound3TimeDerivativeEstimateIsCanonical :
      bound3TimeDerivativeEstimate ≡ bound3TimeDerivativeEstimateStatement

    bound3RemainingBlocker :
      String

    bound3RemainingBlockerIsCanonical :
      bound3RemainingBlocker ≡ Bound3.bound3RemainingBlockerStatement

    receiptBoundary :
      List String

open UltrametricAubinLionsReceipt public

canonicalUltrametricAubinLionsReceipt :
  UltrametricAubinLionsReceipt
canonicalUltrametricAubinLionsReceipt =
  record
    { smoothConvergenceReceipt =
        Smooth.canonicalCarrierNSSmoothConvergenceReceipt
    ; prerequisiteChain =
        Smooth.canonicalCarrierNSAubinLionsPrerequisiteChain
    ; bound3Receipt =
        Bound3.canonicalAubinLionsBound3Receipt
    ; lerayEnergyBoundAlreadyRecorded =
        refl
    ; ultrametricSobolevAlreadyRecorded =
        refl
    ; timeDerivativeBoundRecordedAsTarget =
        refl
    ; timeDerivativeBoundConstructedHere =
        false
    ; timeDerivativeBoundConstructedHereIsFalse =
        refl
    ; bound3LerayEnergyInputRecorded =
        refl
    ; bound3LadyzhenskayaTargetRecorded =
        refl
    ; bound3DiffusionDualNormTargetRecorded =
        refl
    ; bound3PressureGradientTargetRecorded =
        refl
    ; bound3FullProofDerivableFromCurrentLocalObjects =
        refl
    ; bound3CompactnessFlagStillFalse =
        refl
    ; bound3ClayFlagStillFalse =
        refl
    ; bound3RouteComponents =
        canonicalBound3WeakTimeDerivativeRouteComponents
    ; bound3RouteComponentsAreCanonical =
        refl
    ; ladyzhenskayaInterpolationTarget =
        ladyzhenskayaL4FromL2H1Target
    ; ladyzhenskayaInterpolationTargetIsCanonical =
        refl
    ; diffusionDualNormTarget =
        diffusionTermControlledInWMinusOneTwoTarget
    ; diffusionDualNormTargetIsCanonical =
        refl
    ; pressureGradientTarget =
        pressureGradientControlledInWMinusOneTwoTarget
    ; pressureGradientTargetIsCanonical =
        refl
    ; bound3WeakTimeDerivativeEstimateTarget =
        bound3PartialTimeEstimateFromNSDecomposition
          ladyzhenskayaL4FromL2H1Target
          diffusionTermControlledInWMinusOneTwoTarget
          pressureGradientControlledInWMinusOneTwoTarget
    ; bound3WeakTimeDerivativeEstimateTargetIsCanonical =
        refl
    ; bound3RouteRecorded =
        true
    ; bound3RouteRecordedIsTrue =
        refl
    ; bound3EstimateRecordedAsResearchTarget =
        true
    ; bound3EstimateRecordedAsResearchTargetIsTrue =
        refl
    ; bound3EstimateConstructedHere =
        false
    ; bound3EstimateConstructedHereIsFalse =
        refl
    ; bounds =
        canonicalUltrametricAubinLionsBounds
    ; boundsAreCanonical =
        refl
    ; compactnessTheoremInstantiated =
        false
    ; compactnessTheoremInstantiatedIsFalse =
        refl
    ; precompactnessConstructed =
        false
    ; precompactnessConstructedIsFalse =
        refl
    ; continuumLimitExistsConstructed =
        false
    ; continuumLimitExistsConstructedIsFalse =
        refl
    ; limitIsSmoothConstructed =
        false
    ; limitIsSmoothConstructedIsFalse =
        refl
    ; limitSatisfiesContinuumNSConstructed =
        false
    ; limitSatisfiesContinuumNSConstructedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; existingSmoothConvergenceClayFlagStillFalse =
        Smooth.carrierNSSmoothConvergenceDoesNotCloseClay
    ; blockers =
        canonicalUltrametricAubinLionsBlockers
    ; blockersAreCanonical =
        refl
    ; timeDerivativeEstimate =
        timeDerivativeEstimateStatement
    ; timeDerivativeEstimateIsCanonical =
        refl
    ; bound3TimeDerivativeEstimate =
        bound3TimeDerivativeEstimateStatement
    ; bound3TimeDerivativeEstimateIsCanonical =
        refl
    ; bound3RemainingBlocker =
        Bound3.bound3RemainingBlockerStatement
    ; bound3RemainingBlockerIsCanonical =
        refl
    ; receiptBoundary =
        "The three-bound Aubin-Lions route is now a typed target: Leray energy, ultrametric Sobolev uniformity, and weak time-derivative control"
        ∷ "The bound3 weak time-derivative research route is populated by Ladyzhenskaya interpolation, diffusion dual-norm control, and a pressure-gradient W^{-1,2} target"
        ∷ "The recorded bound3 estimate target is ||partial_t u_d||_{L2(0,T;W^{-1,2})} <= C(u0,nu)"
        ∷ "The first two bounds are consumed from existing receipts; the time-derivative estimate is recorded as a derivable target, not a completed proof"
        ∷ Bound3.bound3RemainingBlockerStatement
        ∷ "Carrier-specialized ultrametric Aubin-Lions compactness, C-infinity bootstrap, continuum NS preservation, and BKM passage remain open"
        ∷ "clayNavierStokesPromoted remains false"
        ∷ []
    }

ultrametricAubinLionsCompactnessStillOpen :
  compactnessTheoremInstantiated canonicalUltrametricAubinLionsReceipt
  ≡
  false
ultrametricAubinLionsCompactnessStillOpen =
  refl

ultrametricAubinLionsBound3RouteRecorded :
  bound3RouteRecorded canonicalUltrametricAubinLionsReceipt
  ≡
  true
ultrametricAubinLionsBound3RouteRecorded =
  refl

ultrametricAubinLionsBound3EstimateRecorded :
  bound3EstimateRecordedAsResearchTarget canonicalUltrametricAubinLionsReceipt
  ≡
  true
ultrametricAubinLionsBound3EstimateRecorded =
  refl

ultrametricAubinLionsLadyzhenskayaTargetCanonical :
  ladyzhenskayaInterpolationTarget canonicalUltrametricAubinLionsReceipt
  ≡
  ladyzhenskayaL4FromL2H1Target
ultrametricAubinLionsLadyzhenskayaTargetCanonical =
  refl

ultrametricAubinLionsDiffusionDualNormTargetCanonical :
  diffusionDualNormTarget canonicalUltrametricAubinLionsReceipt
  ≡
  diffusionTermControlledInWMinusOneTwoTarget
ultrametricAubinLionsDiffusionDualNormTargetCanonical =
  refl

ultrametricAubinLionsPressureGradientTargetCanonical :
  pressureGradientTarget canonicalUltrametricAubinLionsReceipt
  ≡
  pressureGradientControlledInWMinusOneTwoTarget
ultrametricAubinLionsPressureGradientTargetCanonical =
  refl

ultrametricAubinLionsBound3EstimateNotConstructed :
  bound3EstimateConstructedHere canonicalUltrametricAubinLionsReceipt
  ≡
  false
ultrametricAubinLionsBound3EstimateNotConstructed =
  refl

ultrametricAubinLionsBound3FullProofStillBlocked :
  Bound3.fullBound3ProofDerivableFromCurrentLocalObjects
    (bound3Receipt canonicalUltrametricAubinLionsReceipt)
  ≡
  false
ultrametricAubinLionsBound3FullProofStillBlocked =
  refl

ultrametricAubinLionsDoesNotPromoteClayNS :
  clayNavierStokesPromoted canonicalUltrametricAubinLionsReceipt
  ≡
  false
ultrametricAubinLionsDoesNotPromoteClayNS =
  refl
