module DASHI.Physics.ThreeBody.BundleIntensity where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.ThreeBody.Regime
open import DASHI.Physics.ThreeBody.Interference

------------------------------------------------------------------------
-- Nearby-bundle and intensity aggregation scaffold for three-body paths.
--
-- This layer remains theorem-thin and intentionally non-final:
-- it exposes local bundle/intensity surfaces without claiming literal QFT,
-- positivity theorems, or completed path-integral dynamics.

record NearbyTrajectoryBundle
  (State : Set)
  : Set₁ where
  field
    pathFamilySurface : ThreeBodyPathFamily State
    neighborhoodWitness :
      Path pathFamilySurface →
      Path pathFamilySurface →
      Set
    bundleAt :
      Path pathFamilySurface →
      Set
    memberPath :
      ∀ p →
      bundleAt p →
      Path pathFamilySurface
    memberAdmissible :
      ∀ p b →
      pathAdmissible pathFamilySurface (memberPath p b)

open NearbyTrajectoryBundle public

record ActionWeightedIntensity
  (State : Set)
  : Set₁ where
  field
    pathActionSurface : ThreeBodyPathAction State
    bundleSurface : NearbyTrajectoryBundle State
    pointIntensity :
      Path (pathFamily (pathActionSurface)) →
      Nat
    bundleIntensity :
      Path (pathFamily (pathActionSurface)) →
      Nat
    bundleIntensityDefSurface : Set
    actionWeightedIntensitySurface : Set

open ActionWeightedIntensity public

record BranchDensityAggregation
  (State : Set)
  : Set₁ where
  field
    branchingSurface : BoundaryGeneratedBranching State
    branchDensity : State → Nat
    branchIntensity : State → Nat
    aggregateBranchDensity : List State → Nat
    aggregateBranchIntensity : List State → Nat
    densityIntensityCompatibilitySurface : Set

open BranchDensityAggregation public

record InteriorBoundaryBundleBehavior
  (State : Set)
  : Set₁ where
  field
    classifier : ThreeBodyRegimeClassifier State
    bundleSurface : NearbyTrajectoryBundle State
    interiorBundleBehavior :
      Path (pathFamilySurface bundleSurface) →
      Set
    boundaryBundleBehavior :
      Path (pathFamilySurface bundleSurface) →
      Set
    interiorVsBoundaryBehaviorSurface : Set
    noGlobalErgodicityClaim : Set

open InteriorBoundaryBundleBehavior public

record ThreeBodyBundleIntensityLayer
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    interferenceLayer :
      ThreeBodyInterferenceLayer State Energy Phase
    nearbyBundleSurface : NearbyTrajectoryBundle State
    actionWeightedIntensitySurface : ActionWeightedIntensity State
    branchDensityAggregationSurface : BranchDensityAggregation State
    interiorBoundaryBundleBehaviorSurface :
      InteriorBoundaryBundleBehavior State

    nearbyBundleDefined : Set
    actionWeightedIntensityDefined : Set
    branchDensityAggregationDefined : Set
    interiorBoundaryBundleBehaviorDefined : Set

    regimeIntensityAggregationSurface : Set
    boundaryGeneratedInterferenceSurface : Set
    localBundleOnlySurface : Set
    noCompletedPathIntegralClaim : Set

open ThreeBodyBundleIntensityLayer public

