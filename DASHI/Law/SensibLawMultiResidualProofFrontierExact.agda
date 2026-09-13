module DASHI.Law.SensibLawMultiResidualProofFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofSearchParetoSaturationExact as Pareto

------------------------------------------------------------------------
-- MULTI-RESIDUAL PROOF FRONTIER
--
-- Search is consumer-relative over the whole currently open proof frontier,
-- not merely a sequence of unrelated one-gap lookups.
------------------------------------------------------------------------

data ProofResidualStatus : Set where
  residualOpen
  residualSatisfied
  residualContested
  residualAuthorityBlocked
  residualUnderidentified
  : ProofResidualStatus

record ProofResidual : Set where
  constructor proofResidual
  field
    residualReference : String
    propositionReference : String
    requiredProducerReference : String
    jurisdictionReference : String
    authorityRequirementReference : String
    salience : Nat
    dependencyReferences : List String
    status : ProofResidualStatus

open ProofResidual public

record ProofFrontier : Set₁ where
  constructor proofFrontier
  field
    consumerReference : String
    residuals : List ProofResidual
    satisfiedPaymentReferences : List String
    contestedCoordinateReferences : List String
    authorityBlockedCoordinateReferences : List String
    frontierReference : String

open ProofFrontier public

record FrontierMoveCandidate : Set₁ where
  constructor frontierMoveCandidate
  field
    targetResidualReference : String
    candidate : Pareto.SearchCandidate
    expectedWholeFrontierReduction : Nat
    sharedDependencyGain : Nat
    moveReference : String

open FrontierMoveCandidate public

record FrontierSchedulingInput : Set₁ where
  constructor frontierSchedulingInput
  field
    frontier : ProofFrontier
    candidatesAcrossOpenResiduals : List FrontierMoveCandidate
    minimumUsefulWholeFrontierReduction : Nat
    schedulingReference : String

open FrontierSchedulingInput public

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data HighestSalienceResidualAutomaticallySelected : Set where
data OneResidualClosedMeansWholeFrontierClosed : Set where
data SharedSourceMeansSharedProofPayment : Set where
data MultiResidualFrontierMeansScalarScore : Set where

highestSalienceDoesNotAutomaticallySelect :
  HighestSalienceResidualAutomaticallySelected → ⊥
highestSalienceDoesNotAutomaticallySelect ()

oneResidualClosedDoesNotCloseFrontier :
  OneResidualClosedMeansWholeFrontierClosed → ⊥
oneResidualClosedDoesNotCloseFrontier ()

sharedSourceDoesNotMeanSharedPayment : SharedSourceMeansSharedProofPayment → ⊥
sharedSourceDoesNotMeanSharedPayment ()

frontierNeedNotScalarise : MultiResidualFrontierMeansScalarScore → ⊥
frontierNeedNotScalarise ()

record MultiResidualFrontierBoundary : Set where
  constructor multiResidualFrontierBoundary
  field
    schedulerSeesWholeOpenFrontier : Bool
    schedulerSeesWholeOpenFrontierIsTrue : schedulerSeesWholeOpenFrontier ≡ true
    residualStatusesRemainDistinct : Bool
    residualStatusesRemainDistinctIsTrue : residualStatusesRemainDistinct ≡ true
    wholeFrontierMayBenefitFromSharedMove : Bool
    wholeFrontierMayBenefitFromSharedMoveIsTrue : wholeFrontierMayBenefitFromSharedMove ≡ true
    oneGapClosureEqualsWholeClosure : Bool
    oneGapClosureEqualsWholeClosureIsFalse : oneGapClosureEqualsWholeClosure ≡ false

canonicalMultiResidualFrontierBoundary : MultiResidualFrontierBoundary
canonicalMultiResidualFrontierBoundary =
  multiResidualFrontierBoundary true refl true refl true refl false refl
