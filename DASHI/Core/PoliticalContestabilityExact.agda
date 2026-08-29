module DASHI.Core.PoliticalContestabilityExact where

------------------------------------------------------------------------
-- POLITICAL CONTESTABILITY
--
-- Technical resolution, democratic contestability, legitimacy and decision
-- authority are intentionally separate coordinates.  This owner is generic;
-- climate/feminist modules supply source-bounded interpretations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record PoliticalContestability : Set₁ where
  constructor politicalContestability
  field
    Alternative : Set
    Participant : Set
    CanContest : Participant → Alternative → Set
    CanSetAgenda : Participant → Set
    CanDeliberate : Participant → Set

open PoliticalContestability public

record ContestabilityReceipt (system : PoliticalContestability) : Set₁ where
  constructor contestabilityReceipt
  field
    participant : Participant system
    alternative : Alternative system
    canContest : CanContest system participant alternative
    canSetAgenda : CanSetAgenda system participant
    canDeliberate : CanDeliberate system participant

open ContestabilityReceipt public

data TechnicalResolution : Set where technicallyResolved : TechnicalResolution
data AdministrativeAuthority : Set where administrativelyAuthorized : AdministrativeAuthority
data DemocraticAuthorization : Set where democraticallyAuthorized : DemocraticAuthorization

-- There is deliberately no constructor from TechnicalResolution to either
-- DemocraticAuthorization or AdministrativeAuthority.  Domain modules must
-- provide their own evidence-bearing bridge if one is justified.

record PoliticalAuthorityBoundary : Set where
  constructor politicalAuthorityBoundary
  field
    technicalResolutionImpliesDemocraticAuthorization : Bool
    technicalResolutionImpliesDemocraticAuthorizationIsFalse :
      technicalResolutionImpliesDemocraticAuthorization ≡ false
    technicalResolutionImpliesAdministrativeAuthority : Bool
    technicalResolutionImpliesAdministrativeAuthorityIsFalse :
      technicalResolutionImpliesAdministrativeAuthority ≡ false
    administrativeAuthorityImpliesPoliticalContestability : Bool
    administrativeAuthorityImpliesPoliticalContestabilityIsFalse :
      administrativeAuthorityImpliesPoliticalContestability ≡ false
    democraticContestabilityEqualsLegitimacy : Bool
    democraticContestabilityEqualsLegitimacyIsFalse :
      democraticContestabilityEqualsLegitimacy ≡ false

canonicalPoliticalAuthorityBoundary : PoliticalAuthorityBoundary
canonicalPoliticalAuthorityBoundary =
  politicalAuthorityBoundary false refl false refl false refl false refl
