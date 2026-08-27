module DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- KALLIS ET AL. 2025: CLAIM-ROLE / AUTHORITY ROUTING
--
-- Giorgos Kallis et al., "Post-growth: the science of wellbeing within
-- planetary boundaries", Lancet Planetary Health 9 (2025), e62--e78,
-- DOI 10.1016/S2542-5196(24)00310-3.
--
-- The review is a synthesis layer, not a replacement raw empirical carrier.
------------------------------------------------------------------------

data ClaimRole : Set where
  empiricalRestatement empiricalSynthesis causalInterpretation
  normativeRecommendation politicalProgramme conceptualFraming : ClaimRole

data AuthorityKind : Set where
  empiricalObservationAuthority reviewSynthesisAuthority causalIdentificationAuthority
  normativeMandateAuthority politicalProgrammeAuthority conceptualInterpretiveAuthority : AuthorityKind

data Authorizes : AuthorityKind → ClaimRole → Set where
  empiricalRestatementAuthorized : Authorizes empiricalObservationAuthority empiricalRestatement
  empiricalSynthesisAuthorized : Authorizes reviewSynthesisAuthority empiricalSynthesis
  causalInterpretationAuthorized : Authorizes causalIdentificationAuthority causalInterpretation
  normativeRecommendationAuthorized : Authorizes normativeMandateAuthority normativeRecommendation
  politicalProgrammeAuthorized : Authorizes politicalProgrammeAuthority politicalProgramme
  conceptualFramingAuthorized : Authorizes conceptualInterpretiveAuthority conceptualFraming

kallisSource : Sources.SourceReference
kallisSource = Sources.kallis2025

kallisReviewAuthority : AuthorityKind
kallisReviewAuthority = reviewSynthesisAuthority

kallisReviewCanSynthesize : Authorizes kallisReviewAuthority empiricalSynthesis
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

------------------------------------------------------------------------
-- Review-level conceptual definition.
------------------------------------------------------------------------

data PostGrowthFamily : Set where
  doughnutEconomics wellbeingEconomics steadyStateEconomics degrowth : PostGrowthFamily

record PostGrowthConcept : Set where
  constructor postGrowthConcept
  field
    pursueGDPGrowthAsObjective : Bool
    targetHumanWellbeing : Bool
    respectPlanetaryBoundaries : Bool

canonicalPostGrowthConcept : PostGrowthConcept
canonicalPostGrowthConcept = postGrowthConcept false true true

------------------------------------------------------------------------
-- The Reel's approximately $15,000 claim.
------------------------------------------------------------------------

data UpstreamEvidenceOwner : Set where
  oneill2018Owner fanning2022Owner collste2021Owner otherReviewEvidence : UpstreamEvidenceOwner

record ReviewRestatement : Set where
  constructor reviewRestatement
  field
    upstreamOwner : UpstreamEvidenceOwner
    amount2011PPP : Nat
    underExistingArrangements : Bool

-- Kallis et al. cite Collste et al. 2021 (their ref. 98) for the statement that
-- the first seven SDGs are achieved at around $15,000 GDP/person (2011 PPP)
-- under existing arrangements.  It is not sourced to Fanning 2022.
gdp15000Restatement : ReviewRestatement
gdp15000Restatement = reviewRestatement collste2021Owner 15000 true

record GDP15000AuthorityBoundary : Set where
  constructor gdp15000AuthorityBoundary
  field
    amountIsApprox15000 : Nat
    amountIsApprox15000Receipt : amountIsApprox15000 ≡ 15000
    immediateEvidenceOwnerIsFanning2022 : Bool
    immediateEvidenceOwnerIsFanning2022IsFalse : immediateEvidenceOwnerIsFanning2022 ≡ false
    immediateEvidenceOwnerIsCollste2021 : Bool
    immediateEvidenceOwnerIsCollste2021IsTrue : immediateEvidenceOwnerIsCollste2021 ≡ true
    meansNothingImprovesAbove15000 : Bool
    meansNothingImprovesAbove15000IsFalse : meansNothingImprovesAbove15000 ≡ false
    establishesContextFreeCausalGDPThreshold : Bool
    establishesContextFreeCausalGDPThresholdIsFalse : establishesContextFreeCausalGDPThreshold ≡ false

canonicalGDP15000AuthorityBoundary : GDP15000AuthorityBoundary
canonicalGDP15000AuthorityBoundary =
  gdp15000AuthorityBoundary 15000 refl false refl true refl false refl false refl

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
    postGrowthEqualsDegrowthByDefinition : Bool
    postGrowthEqualsDegrowthByDefinitionIsFalse : postGrowthEqualsDegrowthByDefinition ≡ false
    reducingGDPIsDefinitionallyTheGoalOfPostGrowth : Bool
    reducingGDPIsDefinitionallyTheGoalOfPostGrowthIsFalse :
      reducingGDPIsDefinitionallyTheGoalOfPostGrowth ≡ false
    politicsOfTransitionRemainsOpenResearchFrontier : Bool
    politicsOfTransitionRemainsOpenResearchFrontierIsTrue :
      politicsOfTransitionRemainsOpenResearchFrontier ≡ true
    claimRoleRequiresTypedAuthority : Bool
    claimRoleRequiresTypedAuthorityIsTrue : claimRoleRequiresTypedAuthority ≡ true

canonicalKallisClaimRoutingBoundary : KallisClaimRoutingBoundary
canonicalKallisClaimRoutingBoundary =
  kallisClaimRoutingBoundary false refl false refl false refl false refl false refl false refl true refl true refl
