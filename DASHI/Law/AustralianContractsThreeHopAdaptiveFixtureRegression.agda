module DASHI.Law.AustralianContractsThreeHopAdaptiveFixtureRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.AustralianContractsThreeHopAdaptiveFixtureExact as Fixture

threeAcceptedHopsRemainExplicit :
  Fixture.hopCount Fixture.canonicalThreeHopAdaptiveFixtureReceipt ≡ 3
threeAcceptedHopsRemainExplicit = refl

freshFrontierRemainsRequiredAfterEveryHop :
  Fixture.freshFrontierAfterEveryHop
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt
    ≡ true
freshFrontierRemainsRequiredAfterEveryHop =
  Fixture.freshFrontierAfterEveryHopIsTrue
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt

fixedQueueStillIsNotConsumed :
  Fixture.fixedUpfrontQueueConsumed
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt
    ≡ false
fixedQueueStillIsNotConsumed =
  Fixture.fixedUpfrontQueueConsumedIsFalse
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt

fixtureStillDoesNotClaimLiveReviewedCampaign :
  Fixture.claimsLiveHumanReviewedCampaign
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt
    ≡ false
fixtureStillDoesNotClaimLiveReviewedCampaign =
  Fixture.claimsLiveHumanReviewedCampaignIsFalse
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt

fixtureStillDoesNotCreateLegalAuthority :
  Fixture.createsLegalAuthority
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt
    ≡ false
fixtureStillDoesNotCreateLegalAuthority =
  Fixture.createsLegalAuthorityIsFalse
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt

fixtureStillDoesNotCreateCurrentLawConclusion :
  Fixture.createsCurrentLawConclusion
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt
    ≡ false
fixtureStillDoesNotCreateCurrentLawConclusion =
  Fixture.createsCurrentLawConclusionIsFalse
    Fixture.canonicalThreeHopAdaptiveFixtureReceipt
