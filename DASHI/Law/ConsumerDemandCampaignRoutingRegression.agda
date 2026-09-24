module DASHI.Law.ConsumerDemandCampaignRoutingRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ConsumerDemandCampaignRoutingExact as Route

boundary : Route.ConsumerDemandCampaignRoutingBoundary
boundary = Route.canonicalConsumerDemandCampaignRoutingBoundary

nonadequacyCanRoute :
  Route.nonadequacyMayRouteResearch boundary ≡ true
nonadequacyCanRoute =
  Route.nonadequacyMayRouteResearchIsTrue boundary

routingIsNotTruthRank :
  Route.routeIsLegalTruthRank boundary ≡ false
routingIsNotTruthRank =
  Route.routeIsLegalTruthRankIsFalse boundary

treatmentCannotSkipReview :
  Route.treatmentDemandMaySkipTreatmentReview boundary ≡ false
treatmentCannotSkipReview =
  Route.treatmentDemandMaySkipTreatmentReviewIsFalse boundary

routingCreatesNoAuthority :
  Route.routingCreatesLegalAuthority boundary ≡ false
routingCreatesNoAuthority =
  Route.routingCreatesLegalAuthorityIsFalse boundary

routingCreatesNoTruth :
  Route.routingCreatesClaimTruth boundary ≡ false
routingCreatesNoTruth =
  Route.routingCreatesClaimTruthIsFalse boundary
