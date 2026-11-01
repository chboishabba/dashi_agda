module DASHI.Physics.ThreeBody.Interference where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.ThreeBody.Regime
open import DASHI.Physics.ThreeBody.PredictiveBoundary

------------------------------------------------------------------------
-- Action-weighted interference scaffold for three-body dynamics.
--
-- This layer is intentionally theorem-thin:
-- it exposes path/action/weight/amplitude/distribution surfaces and
-- boundary-generated branching interfaces without claiming positivity,
-- quantum-complete semantics, or resolved chaos theorems.

record ThreeBodyPathFamily
  (State : Set)
  : Set₁ where
  field
    Path : Set
    pathState : Path → Nat → State
    pathAdmissible : Path → Set
    pathLocalReconstructible : Path → Set

open ThreeBodyPathFamily public

record ThreeBodyPathAction
  (State : Set)
  : Set₁ where
  field
    pathFamily : ThreeBodyPathFamily State
    pathAction : Path pathFamily → Nat
    localActionWindow :
      Nat →
      Path pathFamily →
      Nat
    actionWeight :
      Path pathFamily →
      Nat
    actionWeightDef :
      ∀ p →
        actionWeight p ≡ pathAction p + localActionWindow 0 p

open ThreeBodyPathAction public

record ThreeBodyRegimeWeight
  : Set₁ where
  field
    regimeWeight : ThreeBodyRegime → Nat
    regimeWeightNonnegativeSurface : Set

open ThreeBodyRegimeWeight public

record ThreeBodyRegimeAmplitude
  : Set₁ where
  field
    regimeAmplitude : ThreeBodyRegime → Nat
    regimeAmplitudeFromWeightSurface : Set

open ThreeBodyRegimeAmplitude public

record ThreeBodyRegimeDistribution
  : Set₁ where
  field
    supportRegimes : List ThreeBodyRegime
    regimeMass : ThreeBodyRegime → Nat
    distributionSurface : Set
    normalizationSurface : Set

open ThreeBodyRegimeDistribution public

record BoundaryGeneratedBranching
  (State : Set)
  : Set₁ where
  field
    boundarySource : ChaosBoundary State
    branchFamily : State → Set
    branchPath : ∀ s → branchFamily s → Nat → State
    branchAdmissible : ∀ s → branchFamily s → Set
    branchGeneratedFromBoundary :
      ∀ s →
        ChaosBoundary.boundaryPredicate boundarySource s →
        branchFamily s
    branchInterferenceSurface : Set

open BoundaryGeneratedBranching public

record ThreeBodyInterferenceLayer
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    predictiveLayer :
      ThreeBodyPredictiveBoundaryLayer State Energy Phase
    pathFamilySurface : ThreeBodyPathFamily State
    pathActionSurface : ThreeBodyPathAction State
    regimeWeightSurface : ThreeBodyRegimeWeight
    regimeAmplitudeSurface : ThreeBodyRegimeAmplitude
    regimeDistributionSurface : ThreeBodyRegimeDistribution
    boundaryBranchingSurface : BoundaryGeneratedBranching State

    pathFamilyDefined : Set
    pathActionDefined : Set
    regimeWeightDefined : Set
    regimeAmplitudeDefined : Set
    regimeDistributionDefined : Set
    boundaryGeneratedBranchingDefined : Set

    amplitudeDistributionCompatibilitySurface : Set
    localInterferenceOnlySurface : Set
    noGlobalChaosResolutionClaim : Set

open ThreeBodyInterferenceLayer public
