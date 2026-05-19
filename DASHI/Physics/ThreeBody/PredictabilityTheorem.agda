module DASHI.Physics.ThreeBody.PredictabilityTheorem where

open import Agda.Builtin.Equality using (_≡_)
open import UFTC_Lattice as UFTC using (ConeInterior; ConeInteriorPreserved)
open import Contraction as Contr using (Contractive≢; StrictContraction)
open import CounterexampleHarness using (Counterexample)
open import Ultrametric as UMetric using (Ultrametric)
open import MDL.Core as MDL using (Lyapunov)

open import DASHI.Physics.Closure.Basin as Basin using (Basin)
open import DASHI.Physics.ThreeBody.Step
open import DASHI.Physics.ThreeBody.Regime
open import DASHI.Physics.ThreeBody.PredictiveBoundary
open import DASHI.Physics.ThreeBody.Interference using
  ( ThreeBodyInterferenceLayer
  ; BoundaryGeneratedBranching
  ; ThreeBodyRegimeDistribution
  )
open import DASHI.Physics.ThreeBody.BundleIntensity

------------------------------------------------------------------------
-- Repo-native theorem surfaces for the three-body lane.
--
-- This module does not prove a solved three-body theorem. It names the
-- exact contracts the repo can currently carry:
-- - cone interior vs boundary
-- - local strict contraction when available
-- - basin-relative predictive horizon
-- - boundary-generated branching
-- - bundle/intensity-style regime aggregation

record BoundaryBranchingCompatibility
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    bundleLayer :
      ThreeBodyBundleIntensityLayer State Energy Phase
    branchingWitness :
      BoundaryGeneratedBranching State
    branchingWitnessMatchesInterference :
      branchingWitness
      ≡
      ThreeBodyInterferenceLayer.boundaryBranchingSurface
        (interferenceLayer bundleLayer)
    branchingWitnessMatchesAggregation :
      branchingWitness
      ≡
      BranchDensityAggregation.branchingSurface
        (branchDensityAggregationSurface bundleLayer)
    theoremBoundaryCompatibleWithBranchBoundary :
      State → Set
    branchFamilyAvailableAtBoundary :
      ∀ s →
        theoremBoundaryCompatibleWithBranchBoundary s →
        BoundaryGeneratedBranching.branchFamily
          branchingWitness
          s

open BoundaryBranchingCompatibility public

record ThreeBodyPredictabilityTheorem
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    stepSurface : ThreeBodyStep State
    regimeClassifier : ThreeBodyRegimeClassifier State
    predictiveLayer :
      ThreeBodyPredictiveBoundaryLayer State Energy Phase
    bundleIntensityLayer :
      ThreeBodyBundleIntensityLayer State Energy Phase

    coneSurface : ConeInterior {X = State}
    coneInteriorPreserved :
      ConeInteriorPreserved
        (ThreeBodyStep.step stepSurface)
        coneSurface

    ultrametricSurface : Ultrametric State
    localStrictContraction :
      StrictContraction
        ultrametricSurface
        (ThreeBodyStep.step stepSurface)
    localContractiveBoundary :
      Contractive≢
        ultrametricSurface
        (ThreeBodyStep.step stepSurface)
    localLyapunovSurface :
      Lyapunov (ThreeBodyStep.step stepSurface)

    basinPredictionSurface :
      Basin State
    interiorContractiveGivesHorizon :
      ∀ s →
        UFTC.InInterior coneSurface s →
        Basin.InBasin basinPredictionSurface s →
        LocalPredictiveHorizon State

    boundaryGivesCounterexample :
      ∀ s →
        UFTC.Boundary coneSurface s →
        Counterexample (UFTC.InInterior coneSurface)

    interiorCoherenceSurface :
      ∀ s →
        UFTC.InInterior coneSurface s →
        Set

    boundaryBranchingSurface :
      BoundaryBranchingCompatibility
        State
        Energy
        Phase

    regimeWeightConvergenceSurface :
      ThreeBodyRegimeDistribution

open ThreeBodyPredictabilityTheorem public

record ThreeBodyPredictabilityControlCard
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    theoremSurface :
      ThreeBodyPredictabilityTheorem State Energy Phase
    interiorCoherenceDefined : Set
    boundaryBranchingDefined : Set
    regimeWeightConvergenceDefined : Set
    noGlobalPredictionClaim : Set
    noLiteralQFTClaim : Set

open ThreeBodyPredictabilityControlCard public
