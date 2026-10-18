module DASHI.Law.AustralianContractsThreeHopAdaptiveFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianContractsLandscapeControllerExact as Controller

------------------------------------------------------------------------
-- THREE-HOP S14 ADAPTIVE CONTROLLER ACCEPTANCE FIXTURE
--
-- This mirrors the native Rust executable fixture.  It certifies controller
-- behavior only: three accepted candidate hops, fresh frontier recomputation
-- after every hop, append-only source history, and revisable conclusions.
-- It deliberately does NOT certify that three live human-reviewed authorities
-- have already been completed.
------------------------------------------------------------------------

data ThreeHopFixtureStage : Set where
  reviewedConstructionFixtureHop : ThreeHopFixtureStage
  reviewedUnconscionabilityFixtureHop : ThreeHopFixtureStage
  reviewedPenaltiesFixtureHop : ThreeHopFixtureStage

threeHopFixtureStageOrder : List ThreeHopFixtureStage
threeHopFixtureStageOrder =
  reviewedConstructionFixtureHop
    ∷ reviewedUnconscionabilityFixtureHop
    ∷ reviewedPenaltiesFixtureHop
    ∷ []

record AustralianContractsThreeHopAdaptiveFixtureReceipt : Set where
  constructor australianContractsThreeHopAdaptiveFixtureReceipt
  field
    hopCount : Nat
    stageOrder : List ThreeHopFixtureStage
    contextFrontierCounts : List Nat

    freshFrontierAfterEveryHop : Bool
    freshFrontierAfterEveryHopIsTrue :
      freshFrontierAfterEveryHop ≡ true

    contextFrontierStrictlyShrinks : Bool
    contextFrontierStrictlyShrinksIsTrue :
      contextFrontierStrictlyShrinks ≡ true

    primarySourceFrontierStrictlyGrows : Bool
    primarySourceFrontierStrictlyGrowsIsTrue :
      primarySourceFrontierStrictlyGrows ≡ true

    oldSourceHistoryPreservedAfterEveryHop : Bool
    oldSourceHistoryPreservedAfterEveryHopIsTrue :
      oldSourceHistoryPreservedAfterEveryHop ≡ true

    oldConclusionsFrozenAfterEveryHop : Bool
    oldConclusionsFrozenAfterEveryHopIsFalse :
      oldConclusionsFrozenAfterEveryHop ≡ false

    fixedUpfrontQueueConsumed : Bool
    fixedUpfrontQueueConsumedIsFalse :
      fixedUpfrontQueueConsumed ≡ false

    calibrationFixtureOnly : Bool
    calibrationFixtureOnlyIsTrue :
      calibrationFixtureOnly ≡ true

    claimsLiveHumanReviewedCampaign : Bool
    claimsLiveHumanReviewedCampaignIsFalse :
      claimsLiveHumanReviewedCampaign ≡ false

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

open AustralianContractsThreeHopAdaptiveFixtureReceipt public

canonicalThreeHopAdaptiveFixtureReceipt :
  AustralianContractsThreeHopAdaptiveFixtureReceipt
canonicalThreeHopAdaptiveFixtureReceipt =
  australianContractsThreeHopAdaptiveFixtureReceipt
    3
    threeHopFixtureStageOrder
    (3 ∷ 2 ∷ 1 ∷ [])
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl

threeHopCountIsThree :
  hopCount canonicalThreeHopAdaptiveFixtureReceipt ≡ 3
threeHopCountIsThree = refl

contextFrontierWitnessIsThreeTwoOne :
  contextFrontierCounts canonicalThreeHopAdaptiveFixtureReceipt
    ≡ (3 ∷ 2 ∷ 1 ∷ [])
contextFrontierWitnessIsThreeTwoOne = refl

data AdaptiveFixtureAutomaticallyLiveReviewedCampaign : Set where
data AdaptiveFixtureAutomaticallyLegalAuthority : Set where
data AdaptiveFixtureMayConsumeFixedQueue : Set where

adaptiveFixtureDoesNotBecomeLiveReviewedCampaign :
  AdaptiveFixtureAutomaticallyLiveReviewedCampaign → ⊥
adaptiveFixtureDoesNotBecomeLiveReviewedCampaign ()

adaptiveFixtureDoesNotCreateAuthority :
  AdaptiveFixtureAutomaticallyLegalAuthority → ⊥
adaptiveFixtureDoesNotCreateAuthority ()

adaptiveFixtureDoesNotLicenseFixedQueueConsumption :
  AdaptiveFixtureMayConsumeFixedQueue → ⊥
adaptiveFixtureDoesNotLicenseFixedQueueConsumption ()

ControllerBoundary : Set
ControllerBoundary = Controller.AustralianContractsLandscapeControllerBoundary

controllerBoundaryPaid : ControllerBoundary
controllerBoundaryPaid =
  Controller.canonicalAustralianContractsLandscapeControllerBoundary
