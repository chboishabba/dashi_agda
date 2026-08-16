module DASHI.Governance.ConsentDistrustDualityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Manufacturing consent / manufacturing distrust duality.
--
-- Herman and Chomsky, "Manufacturing Consent: The Political Economy of the
-- Mass Media" (1988). Book; no DOI assigned.
--
-- The source motivates the institutional-media vocabulary only.  The exact
-- two-route relative-authority algebra below is a DASHI construction.
------------------------------------------------------------------------

data AuthorityShiftRoute : Set where
  promotePreferred : AuthorityShiftRoute
  demoteAlternative : AuthorityShiftRoute

record CredibilityPair : Set₁ where
  field
    Preferred : Set
    Alternative : Set
    Credibility : Set
    preferredCredibility : Preferred → Credibility
    alternativeCredibility : Alternative → Credibility

record RelativeAuthorityShift
  (C : CredibilityPair) : Set₁ where
  field
    route : AuthorityShiftRoute
    PreferredAgent : CredibilityPair.Preferred C
    AlternativeAgent : CredibilityPair.Alternative C
    beforePreferred : CredibilityPair.Credibility C
    beforeAlternative : CredibilityPair.Credibility C
    afterPreferred : CredibilityPair.Credibility C
    afterAlternative : CredibilityPair.Credibility C

------------------------------------------------------------------------
-- The two routes are intentionally different constructors of one higher-level
-- relation.  Nothing here asserts that they have equal empirical magnitude.
------------------------------------------------------------------------

record PreferredPromotion
  (C : CredibilityPair) : Set₁ where
  field
    preferred : CredibilityPair.Preferred C
    alternative : CredibilityPair.Alternative C
    beforePreferred : CredibilityPair.Credibility C
    beforeAlternative : CredibilityPair.Credibility C
    afterPreferred : CredibilityPair.Credibility C

record AlternativeDemotion
  (C : CredibilityPair) : Set₁ where
  field
    preferred : CredibilityPair.Preferred C
    alternative : CredibilityPair.Alternative C
    beforePreferred : CredibilityPair.Credibility C
    beforeAlternative : CredibilityPair.Credibility C
    afterAlternative : CredibilityPair.Credibility C

promotionIsRelativeShift :
  ∀ {C : CredibilityPair} →
  PreferredPromotion C →
  RelativeAuthorityShift C
promotionIsRelativeShift Cshift =
  record
    { route = promotePreferred
    ; PreferredAgent = PreferredPromotion.preferred Cshift
    ; AlternativeAgent = PreferredPromotion.alternative Cshift
    ; beforePreferred = PreferredPromotion.beforePreferred Cshift
    ; beforeAlternative = PreferredPromotion.beforeAlternative Cshift
    ; afterPreferred = PreferredPromotion.afterPreferred Cshift
    ; afterAlternative = PreferredPromotion.beforeAlternative Cshift
    }

demotionIsRelativeShift :
  ∀ {C : CredibilityPair} →
  AlternativeDemotion C →
  RelativeAuthorityShift C
demotionIsRelativeShift Cshift =
  record
    { route = demoteAlternative
    ; PreferredAgent = AlternativeDemotion.preferred Cshift
    ; AlternativeAgent = AlternativeDemotion.alternative Cshift
    ; beforePreferred = AlternativeDemotion.beforePreferred Cshift
    ; beforeAlternative = AlternativeDemotion.beforeAlternative Cshift
    ; afterPreferred = AlternativeDemotion.beforePreferred Cshift
    ; afterAlternative = AlternativeDemotion.afterAlternative Cshift
    }

promotingPreferredIsNotDefinitionallyDemotingAlternative :
  promotePreferred ≡ demoteAlternative → ⊥
promotingPreferredIsNotDefinitionallyDemotingAlternative ()

record ConsentDistrustBoundary : Set where
  constructor consentDistrustBoundary
  field
    promotingPreferredEqualsDemotingAlternative : Bool
    bothMayChangeRelativeAuthority : Bool
    distrustOfOneInstitutionProvesAnotherReliable : Bool
    legitimateInstitutionalFailureImpliesUniversalDistrust : Bool
    empiricalMagnitudeRequiresEvidence : Bool

canonicalConsentDistrustBoundary : ConsentDistrustBoundary
canonicalConsentDistrustBoundary =
  consentDistrustBoundary false true false false true
