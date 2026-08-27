module DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- KALLIS ET AL. 2025: CLAIM-ROLE / AUTHORITY ROUTING
--
-- The review is a synthesis layer.  This module does not reconstruct all of
-- its prose claims.  Instead it types the authority required by different
-- possible claim roles so empirical evidence cannot be promoted silently into
-- causal, normative or political authority.
------------------------------------------------------------------------

data ClaimRole : Set where
  empiricalRestatement
  empiricalSynthesis
  causalInterpretation
  normativeRecommendation
  politicalProgramme
  conceptualFraming
  : ClaimRole

data AuthorityKind : Set where
  empiricalObservationAuthority
  reviewSynthesisAuthority
  causalIdentificationAuthority
  normativeMandateAuthority
  politicalProgrammeAuthority
  conceptualInterpretiveAuthority
  : AuthorityKind

data Authorizes : AuthorityKind → ClaimRole → Set where
  empiricalRestatementAuthorized :
    Authorizes empiricalObservationAuthority empiricalRestatement
  empiricalSynthesisAuthorized :
    Authorizes reviewSynthesisAuthority empiricalSynthesis
  causalInterpretationAuthorized :
    Authorizes causalIdentificationAuthority causalInterpretation
  normativeRecommendationAuthorized :
    Authorizes normativeMandateAuthority normativeRecommendation
  politicalProgrammeAuthorized :
    Authorizes politicalProgrammeAuthority politicalProgramme
  conceptualFramingAuthorized :
    Authorizes conceptualInterpretiveAuthority conceptualFraming

kallisSource : Sources.SourceReference
kallisSource = Sources.kallis2025

kallisReviewAuthority : AuthorityKind
kallisReviewAuthority = reviewSynthesisAuthority

kallisReviewCanSynthesize :
  Authorizes kallisReviewAuthority empiricalSynthesis
kallisReviewCanSynthesize = empiricalSynthesisAuthorized

kallisReviewAloneDoesNotAuthorizeCausalInterpretation :
  Authorizes kallisReviewAuthority causalInterpretation → ⊥
kallisReviewAloneDoesNotAuthorizeCausalInterpretation ()

kallisReviewAloneDoesNotAuthorizeNormativeRecommendation :
  Authorizes kallisReviewAuthority normativeRecommendation → ⊥
kallisReviewAloneDoesNotAuthorizeNormativeRecommendation ()

kallisReviewAloneDoesNotAuthorizePoliticalProgramme :
  Authorizes kallisReviewAuthority politicalProgramme → ⊥
kallisReviewAloneDoesNotAuthorizePoliticalProgramme ()

record ClaimRoute : Set₁ where
  constructor claimRoute
  field
    role : ClaimRole
    authority : AuthorityKind
    authorization : Authorizes authority role

canonicalKallisSynthesisRoute : ClaimRoute
canonicalKallisSynthesisRoute =
  claimRoute empiricalSynthesis reviewSynthesisAuthority empiricalSynthesisAuthorized

record KallisClaimRoutingBoundary : Set where
  constructor kallisClaimRoutingBoundary
  field
    reviewSynthesisRetroactivelyUpgradesEarlierEmpiricalAuthority : Bool
    reviewSynthesisRetroactivelyUpgradesEarlierEmpiricalAuthorityIsFalse :
      reviewSynthesisRetroactivelyUpgradesEarlierEmpiricalAuthority ≡ false
    reviewIdentityAloneAuthorizesCausalInterpretation : Bool
    reviewIdentityAloneAuthorizesCausalInterpretationIsFalse :
      reviewIdentityAloneAuthorizesCausalInterpretation ≡ false
    reviewIdentityAloneAuthorizesNormativeRecommendation : Bool
    reviewIdentityAloneAuthorizesNormativeRecommendationIsFalse :
      reviewIdentityAloneAuthorizesNormativeRecommendation ≡ false
    reviewIdentityAloneDefinesPoliticalProgramme : Bool
    reviewIdentityAloneDefinesPoliticalProgrammeIsFalse :
      reviewIdentityAloneDefinesPoliticalProgramme ≡ false
    claimRoleRequiresTypedAuthority : Bool
    claimRoleRequiresTypedAuthorityIsTrue :
      claimRoleRequiresTypedAuthority ≡ true

canonicalKallisClaimRoutingBoundary : KallisClaimRoutingBoundary
canonicalKallisClaimRoutingBoundary =
  kallisClaimRoutingBoundary false refl false refl false refl false refl true refl
