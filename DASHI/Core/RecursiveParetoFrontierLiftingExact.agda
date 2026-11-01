module DASHI.Core.RecursiveParetoFrontierLiftingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ExperimentalCoordinateDesignExact as Design

------------------------------------------------------------------------
-- RECURSIVE PARETO FRONTIER LIFTING
--
-- A higher representational level may expose a much larger axis language.
-- Adaptive search need not materialise every axis or every candidate profile.
-- Instead it may lift only residual-relevant coordinates from the current
-- Pareto frontier, preserving old costs on embedded axes and requiring a new
-- admission receipt before theorem search or physical experimentation.
------------------------------------------------------------------------

record FrontierLayer : Set₁ where
  constructor frontierLayer
  field
    Axis : Set
    Candidate : Set
    Active : Candidate → Set
    cost : Axis → Candidate → Nat
    axisReference : Axis → String
    candidateReference : Candidate → String

open FrontierLayer public

record FrontierLift (lower upper : FrontierLayer) : Set₁ where
  constructor frontierLift
  field
    embedAxis : Axis lower → Axis upper
    liftCandidate : Candidate lower → Candidate upper
    activePreserved :
      (candidate : Candidate lower) →
      Active lower candidate →
      Active upper (liftCandidate candidate)
    oldCostPreserved :
      (axis : Axis lower) →
      (candidate : Candidate lower) →
      cost upper (embedAxis axis) (liftCandidate candidate)
      ≡ cost lower axis candidate
    liftReference : String

open FrontierLift public

record ResidualRelevantMaterialisation
    {lower upper : FrontierLayer}
    (lift : FrontierLift lower upper) : Set₁ where
  constructor residualRelevantMaterialisation
  field
    MaterialisedAxis : Set
    includeMaterialised : MaterialisedAxis → Axis upper
    residualRelevant : MaterialisedAxis → Set
    materialisationReference : MaterialisedAxis → String
    consumerReference : String

open ResidualRelevantMaterialisation public

record AdmittedFrontierRefinement
    {lower upper : FrontierLayer}
    (lift : FrontierLift lower upper) : Set₁ where
  constructor admittedFrontierRefinement
  field
    materialisation : ResidualRelevantMaterialisation lift
    proofSearchAdmission : ProofSearch.RouteAdmission
    experimentDesignReference : String
    noSilentHypothesisExpansionReference : String

open AdmittedFrontierRefinement public

liveProofSearchAfterRefinement :
  ∀ {lower upper : FrontierLayer}
    {lift : FrontierLift lower upper} →
  AdmittedFrontierRefinement lift → ProofSearch.LiveProofSearch
liveProofSearchAfterRefinement refinement =
  ProofSearch.elaborateRoute (proofSearchAdmission refinement)

record RecursiveParetoFrontierBoundary : Set where
  constructor recursiveParetoFrontierBoundary
  field
    higherAxisCapacityForcesFullMaterialisation : Bool
    higherAxisCapacityForcesFullMaterialisationIsFalse :
      higherAxisCapacityForcesFullMaterialisation ≡ false
    residualRelevantRefinementMayOpenOnlySelectedAxes : Bool
    residualRelevantRefinementMayOpenOnlySelectedAxesIsTrue :
      residualRelevantRefinementMayOpenOnlySelectedAxes ≡ true
    frontierLiftMaySilentlyChangeOldAxisCosts : Bool
    frontierLiftMaySilentlyChangeOldAxisCostsIsFalse :
      frontierLiftMaySilentlyChangeOldAxisCosts ≡ false
    paretoFrontierRefinementCreatesProofAuthority : Bool
    paretoFrontierRefinementCreatesProofAuthorityIsFalse :
      paretoFrontierRefinementCreatesProofAuthority ≡ false
    experimentalCoordinateCreatesPhysicalDimensionAutomatically : Bool
    experimentalCoordinateCreatesPhysicalDimensionAutomaticallyIsFalse :
      experimentalCoordinateCreatesPhysicalDimensionAutomatically ≡ false

canonicalRecursiveParetoFrontierBoundary : RecursiveParetoFrontierBoundary
canonicalRecursiveParetoFrontierBoundary =
  recursiveParetoFrontierBoundary false refl true refl false refl false refl false refl

existingNDimBoundary : NDim.NDimParetoHyperfabricBoundary
existingNDimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary

existingExperimentalCoordinateBoundary : Design.ExperimentalCoordinateBoundary
existingExperimentalCoordinateBoundary = Design.canonicalExperimentalCoordinateBoundary

existingProofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
existingProofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary
