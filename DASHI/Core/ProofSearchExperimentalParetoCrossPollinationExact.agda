module DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Recursive

------------------------------------------------------------------------
-- PROOF SEARCH / EXPERIMENTAL DESIGN / PARETO FRONTIER WELD
--
-- Proof routes and experiments can both refine a live frontier, but they carry
-- different authority.  A discriminating experiment may redirect proof search;
-- it cannot itself become a theorem leaf.  A theorem route may reduce a formal
-- frontier; it does not create permission to manipulate a physical system.
------------------------------------------------------------------------

data RefinementProducerKind : Set where
  repositoryReuse
  sourceReconstruction
  symbolicProofRoute
  numericalExperiment
  physicalMeasurement
  derivedExperimentalCoordinate
  : RefinementProducerKind

producerAuthority : RefinementProducerKind → ProofSearch.TheoremAuthority
producerAuthority repositoryReuse = ProofSearch.derivedRepositoryTheorem
producerAuthority sourceReconstruction = ProofSearch.sourceTheoremMatched
producerAuthority symbolicProofRoute = ProofSearch.conditionalInterface
producerAuthority numericalExperiment = ProofSearch.analogyOnly
producerAuthority physicalMeasurement = ProofSearch.conditionalInterface
producerAuthority derivedExperimentalCoordinate = ProofSearch.analogyOnly

record FrontierRefinementProposal : Set₁ where
  constructor frontierRefinementProposal
  field
    producerKind : RefinementProducerKind
    residualTargetReference : String
    consumerReference : String
    paretoAxisReference : String
    expectedFrontierReductionReference : String
    sameObjectReference : String
    authorityReference : String

open FrontierRefinementProposal public

record AdmittedProofSearchRefinement (proposal : FrontierRefinementProposal) : Set where
  constructor admittedProofSearchRefinement
  field
    routeAdmission : ProofSearch.RouteAdmission

open AdmittedProofSearchRefinement public

elaborateAdmittedProposal :
  {proposal : FrontierRefinementProposal} →
  AdmittedProofSearchRefinement proposal →
  ProofSearch.LiveProofSearch
elaborateAdmittedProposal admitted =
  ProofSearch.elaborateRoute (routeAdmission admitted)

record ExperimentalDiscriminatorRefinement : Set₁ where
  constructor experimentalDiscriminatorRefinement
  field
    coordinateRole : Design.CoordinateRole
    collisionReference : String
    calibrationOrDerivationReference : String
    residualReductionReference : String
    physicalAuthoritySeparatelyRequired : Bool

open ExperimentalDiscriminatorRefinement public

record ProofSearchExperimentalParetoBoundary : Set where
  constructor proofSearchExperimentalParetoBoundary
  field
    experimentMayRedirectProofSearch : Bool
    experimentMayRedirectProofSearchIsTrue : experimentMayRedirectProofSearch ≡ true
    numericalExperimentDirectlyClosesFormalLeaf : Bool
    numericalExperimentDirectlyClosesFormalLeafIsFalse : numericalExperimentDirectlyClosesFormalLeaf ≡ false
    paretoUndominatedRouteAutomaticallyMovesProgrammeFrontier : Bool
    paretoUndominatedRouteAutomaticallyMovesProgrammeFrontierIsFalse :
      paretoUndominatedRouteAutomaticallyMovesProgrammeFrontier ≡ false
    theoremRouteCreatesPhysicalExperimentAuthority : Bool
    theoremRouteCreatesPhysicalExperimentAuthorityIsFalse :
      theoremRouteCreatesPhysicalExperimentAuthority ≡ false
    derivedCoordinateMayIncreaseDiscrimination : Bool
    derivedCoordinateMayIncreaseDiscriminationIsTrue : derivedCoordinateMayIncreaseDiscrimination ≡ true
    recursiveFrontierCanOpenResidualRelevantCoordinatesOnly : Bool
    recursiveFrontierCanOpenResidualRelevantCoordinatesOnlyIsTrue :
      recursiveFrontierCanOpenResidualRelevantCoordinatesOnly ≡ true

canonicalProofSearchExperimentalParetoBoundary : ProofSearchExperimentalParetoBoundary
canonicalProofSearchExperimentalParetoBoundary =
  proofSearchExperimentalParetoBoundary true refl false refl false refl false refl true refl true refl

existingRecursiveBoundary : Recursive.RecursiveParetoFrontierBoundary
existingRecursiveBoundary = Recursive.canonicalRecursiveParetoFrontierBoundary
