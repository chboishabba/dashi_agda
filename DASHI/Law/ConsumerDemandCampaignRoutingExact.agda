module DASHI.Law.ConsumerDemandCampaignRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Nonfactorability / consumer-demand routing into existing campaign gates.
--
-- This is routing, not legal inference.  A missing consumer coordinate names
-- a research class; it does not establish the missing proposition.
------------------------------------------------------------------------

data ConsumerResearchKind : Set where
  acquireSource : ConsumerResearchKind
  recoverProvenance : ConsumerResearchKind
  reviewTreatment : ConsumerResearchKind
  resolveTemporal : ConsumerResearchKind
  resolveJurisdiction : ConsumerResearchKind
  reviewFact : ConsumerResearchKind
  reviewBurdenOrException : ConsumerResearchKind
  resolveSemanticIdentity : ConsumerResearchKind

data CampaignRoute : Set where
  primarySourceRoute : CampaignRoute
  treatmentReviewRoute : CampaignRoute
  temporalRoute : CampaignRoute
  contextRoute : CampaignRoute

route : ConsumerResearchKind → CampaignRoute
route acquireSource = primarySourceRoute
route recoverProvenance = primarySourceRoute
route reviewTreatment = treatmentReviewRoute
route resolveTemporal = temporalRoute
route resolveJurisdiction = contextRoute
route reviewFact = contextRoute
route reviewBurdenOrException = contextRoute
route resolveSemanticIdentity = contextRoute

treatmentDemandRoutesToTreatmentGate :
  route reviewTreatment ≡ treatmentReviewRoute
treatmentDemandRoutesToTreatmentGate = refl

sourceDemandRoutesToSourceGate :
  route acquireSource ≡ primarySourceRoute
sourceDemandRoutesToSourceGate = refl

record ConsumerDemandCampaignRoutingBoundary : Set where
  constructor consumerDemandCampaignRoutingBoundary
  field
    nonadequacyMayRouteResearch : Bool
    nonadequacyMayRouteResearchIsTrue :
      nonadequacyMayRouteResearch ≡ true

    routeIsLegalTruthRank : Bool
    routeIsLegalTruthRankIsFalse :
      routeIsLegalTruthRank ≡ false

    treatmentDemandMaySkipTreatmentReview : Bool
    treatmentDemandMaySkipTreatmentReviewIsFalse :
      treatmentDemandMaySkipTreatmentReview ≡ false

    routingCreatesLegalAuthority : Bool
    routingCreatesLegalAuthorityIsFalse :
      routingCreatesLegalAuthority ≡ false

    routingCreatesClaimTruth : Bool
    routingCreatesClaimTruthIsFalse :
      routingCreatesClaimTruth ≡ false

open ConsumerDemandCampaignRoutingBoundary public

canonicalConsumerDemandCampaignRoutingBoundary :
  ConsumerDemandCampaignRoutingBoundary
canonicalConsumerDemandCampaignRoutingBoundary =
  consumerDemandCampaignRoutingBoundary
    true refl
    false refl
    false refl
    false refl
    false refl

data ResearchRouteAutomaticallyTruthRank : Set where
data TreatmentDemandAutomaticallyReviewed : Set where
data ResearchRouteAutomaticallyAuthority : Set where

researchRouteIsNotTruthRank :
  ResearchRouteAutomaticallyTruthRank → ⊥
researchRouteIsNotTruthRank ()

treatmentDemandDoesNotBecomeReviewedTreatment :
  TreatmentDemandAutomaticallyReviewed → ⊥
treatmentDemandDoesNotBecomeReviewedTreatment ()

researchRouteDoesNotCreateAuthority :
  ResearchRouteAutomaticallyAuthority → ⊥
researchRouteDoesNotCreateAuthority ()
