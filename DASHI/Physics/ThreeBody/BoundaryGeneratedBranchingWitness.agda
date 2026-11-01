module DASHI.Physics.ThreeBody.BoundaryGeneratedBranchingWitness where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Product using (Σ; _,_)

open import DASHI.Physics.Closure.Basin as Basin using (Basin)
open import DASHI.Physics.ThreeBody.Regime
open import DASHI.Physics.ThreeBody.Interference as Interf
  using (BoundaryGeneratedBranching; ThreeBodyInterferenceLayer; ThreeBodyRegimeWeight)
open import DASHI.Physics.ThreeBody.BundleIntensity as BI
  using (ThreeBodyBundleIntensityLayer)
open import DASHI.Physics.ThreeBody.PredictabilityTheorem

------------------------------------------------------------------------
-- Constructive witness packaging for the current boundary-generated branching
-- lane.
--
-- This module still does not prove a global chaos theorem. It packages one
-- explicit branch witness sourced from the already-landed theorem/bundle
-- surfaces so downstream code can depend on an actual object rather than a
-- bare compatibility predicate.

record BoundaryGeneratedBranchingWitness
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    predictabilityTheorem :
      ThreeBodyPredictabilityTheorem State Energy Phase
    boundaryState : State
    boundaryCompatibility :
      BoundaryBranchingCompatibility.theoremBoundaryCompatibleWithBranchBoundary
        (ThreeBodyPredictabilityTheorem.boundaryBranchingSurface predictabilityTheorem)
        boundaryState
    branchMember :
      BoundaryGeneratedBranching.branchFamily
        (BoundaryBranchingCompatibility.branchingWitness
          (ThreeBodyPredictabilityTheorem.boundaryBranchingSurface predictabilityTheorem))
        boundaryState
    boundaryRegime : ThreeBodyRegime
    boundaryRegimeWitness :
      ThreeBodyRegimeClassifier.classify
        (ThreeBodyPredictabilityTheorem.regimeClassifier predictabilityTheorem)
        boundaryState
      ≡
      boundaryRegime
    boundaryOnConeEvidence :
      ThreeBodyRegimeClassifier.onConeBoundary
        (ThreeBodyPredictabilityTheorem.regimeClassifier predictabilityTheorem)
        boundaryState
    branchMemberMatchesGeneratedBoundary :
      branchMember
      ≡
      BoundaryBranchingCompatibility.branchFamilyAvailableAtBoundary
        (ThreeBodyPredictabilityTheorem.boundaryBranchingSurface predictabilityTheorem)
        boundaryState
        boundaryCompatibility
    branchTime : Nat
    branchState : State
    branchStateDef :
      branchState
      ≡
      BoundaryGeneratedBranching.branchPath
        (BoundaryBranchingCompatibility.branchingWitness
          (ThreeBodyPredictabilityTheorem.boundaryBranchingSurface predictabilityTheorem))
        boundaryState
        branchMember
        branchTime
    branchStateInBasin :
      Basin.InBasin
        (ThreeBodyPredictabilityTheorem.basinPredictionSurface predictabilityTheorem)
        branchState
    branchWeightObserved :
      Nat
    branchWeightObservedDef :
      branchWeightObserved
      ≡
      ThreeBodyRegimeWeight.regimeWeight
        (Interf.regimeWeightSurface
          (BI.interferenceLayer
            (BoundaryBranchingCompatibility.bundleLayer
              (ThreeBodyPredictabilityTheorem.boundaryBranchingSurface predictabilityTheorem))))
        boundaryRegime

  boundaryCompatibilitySurface :
    BoundaryBranchingCompatibility State Energy Phase
  boundaryCompatibilitySurface =
    ThreeBodyPredictabilityTheorem.boundaryBranchingSurface predictabilityTheorem

  witnessBundleLayer :
    ThreeBodyBundleIntensityLayer State Energy Phase
  witnessBundleLayer =
    BoundaryBranchingCompatibility.bundleLayer boundaryCompatibilitySurface

  witnessInterferenceLayer :
    ThreeBodyInterferenceLayer State Energy Phase
  witnessInterferenceLayer =
    BI.interferenceLayer witnessBundleLayer

  witnessBranchingSurface :
    BoundaryGeneratedBranching State
  witnessBranchingSurface =
    BoundaryBranchingCompatibility.branchingWitness boundaryCompatibilitySurface

  branchPathState : Nat → State
  branchPathState =
    BoundaryGeneratedBranching.branchPath
      witnessBranchingSurface
      boundaryState
      branchMember

  theoremGeneratedBranch :
    BoundaryGeneratedBranching.branchFamily
      witnessBranchingSurface
      boundaryState
  theoremGeneratedBranch =
    BoundaryBranchingCompatibility.branchFamilyAvailableAtBoundary
      boundaryCompatibilitySurface
      boundaryState
      boundaryCompatibility

  witnessBranchWeightSurface : ThreeBodyRegimeWeight
  witnessBranchWeightSurface =
    Interf.regimeWeightSurface witnessInterferenceLayer

  boundaryToWeightedBranchChain :
    Σ State
      (λ s →
        Σ (ThreeBodyRegimeClassifier.onConeBoundary
             (ThreeBodyPredictabilityTheorem.regimeClassifier predictabilityTheorem)
             s)
              (λ _ →
            Σ (BoundaryGeneratedBranching.branchFamily witnessBranchingSurface s)
              (λ _ →
                Σ ThreeBodyRegime
                  (λ r →
                    ThreeBodyRegimeWeight.regimeWeight witnessBranchWeightSurface r
                    ≡ branchWeightObserved))))
  boundaryToWeightedBranchChain =
    boundaryState ,
    boundaryOnConeEvidence ,
    branchMember ,
    boundaryRegime ,
    sym branchWeightObservedDef

open BoundaryGeneratedBranchingWitness public
