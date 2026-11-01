module DASHI.Core.PersonIdentityAttributionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data IdentityCoordinate : Set where
  fullLegalOrPublishedName : IdentityCoordinate
  middleNameOrInitial : IdentityCoordinate
  dateOrAge : IdentityCoordinate
  institution : IdentityCoordinate
  roleTitle : IdentityCoordinate
  technicalField education location familyOrAlias sourcePersistentIdentifier : IdentityCoordinate


data IdentityStatus : Set where
  identitySourceBacked : IdentityStatus
  identityPartial : IdentityStatus
  identityNotLocated : IdentityStatus
  identityContradicted : IdentityStatus

record IdentityReceipt : Set where
  constructor identity-receipt
  field
    eventSubject : String
    technicalSubject : String
    coordinates : List IdentityCoordinate
    status : IdentityStatus
    sourceReference : String
    boundedReading : String
open IdentityReceipt public

record IdentityAttributionBoundary : Set where
  constructor identity-attribution-boundary
  field
    sameNameImpliesSamePerson : Bool
    sameNameImpliesSamePersonIsFalse : sameNameImpliesSamePerson ≡ false
    sameInstitutionImpliesSamePerson : Bool
    sameInstitutionImpliesSamePersonIsFalse : sameInstitutionImpliesSamePerson ≡ false
    sameFieldImpliesSamePerson : Bool
    sameFieldImpliesSamePersonIsFalse : sameFieldImpliesSamePerson ≡ false
    matchingInitialsImpliesSamePerson : Bool
    matchingInitialsImpliesSamePersonIsFalse : matchingInitialsImpliesSamePerson ≡ false
    secondaryAliasImpliesPrimaryIdentity : Bool
    secondaryAliasImpliesPrimaryIdentityIsFalse : secondaryAliasImpliesPrimaryIdentity ≡ false
    sourceBackedIdentityCanPermitCapabilityAttribution : Bool
    sourceBackedIdentityCanPermitCapabilityAttributionIsTrue : sourceBackedIdentityCanPermitCapabilityAttribution ≡ true
canonicalIdentityAttributionBoundary : IdentityAttributionBoundary
canonicalIdentityAttributionBoundary = identity-attribution-boundary false refl false refl false refl false refl false refl true refl

data IdentityReverseTarget : Set where
  acquireFullNameWeld : IdentityReverseTarget
  acquireAliasOrFormerNameWeld : IdentityReverseTarget
  acquireDateOrAgeWeld : IdentityReverseTarget
  acquireInstitutionRoleWeld acquirePersistentIdentifierWeld acquirePrimarySamePersonStatement : IdentityReverseTarget
