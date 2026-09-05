module DASHI.Core.ScientificWorkAttributionExact where

------------------------------------------------------------------------
-- SCIENTIFIC WORK ATTRIBUTION / NON-LAUNDERING CORE
--
-- DASHI attribution policy requires source-derived claims to preserve the
-- distinction between source claim, repository reconstruction, cross-source
-- inference, and DASHI theorem.  This module adds the person/work analogue:
--
--   affiliation != authorship != contribution != programme ownership
--   != formalisation ownership != downstream inference ownership.
--
-- A person's name may be attached to a scientific object only under the role
-- actually supported by the cited provenance.  In particular, institutional
-- affiliation does not silently promote a person into inventor, author, PI,
-- team lead, or owner of every programme conducted by that institution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Attribution fibres.
------------------------------------------------------------------------

data AttributionRole : Set where
  namedAuthor
  namedInventor
  namedPrincipalInvestigator
  namedTeamMember
  namedTechnicalLead
  institutionalResearchRole
  institutionalLeadershipRole
  affiliationOnly
  reportedRelationshipOnly
  : AttributionRole

data SourceStrength : Set where
  primaryPatentRecord
  primaryPublicationRecord
  primaryInstitutionalRecord
  officialDocumentRepeatingPublicReporting
  secondaryReportingOnly
  unresolvedSourceStrength
  : SourceStrength

data ClaimOwner : Set where
  externalSourceOwner
  dashiFormalisationOwner
  dashiInferenceOwner
  unresolvedClaimOwner
  : ClaimOwner

record ScientificWorkAttribution : Set where
  constructor scientific-work-attribution
  field
    personName : String
    scientificObject : String
    institutionOrProgramme : String
    attributionRole : AttributionRole
    sourceStrength : SourceStrength
    sourceLocator : String
    boundedReading : String
    ownerOfClaim : ClaimOwner

open ScientificWorkAttribution public

------------------------------------------------------------------------
-- Relationships between people are their own evidence objects.  They are not
-- generated merely because two people occur in the same investigative roster.
------------------------------------------------------------------------

record PersonRelationshipAttribution : Set where
  constructor person-relationship-attribution
  field
    leftPerson : String
    rightPerson : String
    relationshipClaim : String
    relationshipSourceStrength : SourceStrength
    relationshipSourceLocator : String
    relationshipReading : String

open PersonRelationshipAttribution public

------------------------------------------------------------------------
-- Explicit no-promotion receipts.
------------------------------------------------------------------------

record ScientificAttributionBoundary : Set where
  constructor scientific-attribution-boundary
  field
    affiliationImpliesAuthorship : Bool
    affiliationImpliesAuthorshipIsFalse : affiliationImpliesAuthorship ≡ false

    affiliationImpliesInventorship : Bool
    affiliationImpliesInventorshipIsFalse : affiliationImpliesInventorship ≡ false

    institutionalLeadershipImpliesAuthorshipOfEveryProgramme : Bool
    institutionalLeadershipImpliesAuthorshipOfEveryProgrammeIsFalse :
      institutionalLeadershipImpliesAuthorshipOfEveryProgramme ≡ false

    sameProgrammeImpliesSameContribution : Bool
    sameProgrammeImpliesSameContributionIsFalse :
      sameProgrammeImpliesSameContribution ≡ false

    sameInstitutionImpliesProfessionalRelationship : Bool
    sameInstitutionImpliesProfessionalRelationshipIsFalse :
      sameInstitutionImpliesProfessionalRelationship ≡ false

    congressionalMentionUpgradesUnderlyingPressClaimToPrimaryTechnicalEvidence : Bool
    congressionalMentionUpgradesUnderlyingPressClaimToPrimaryTechnicalEvidenceIsFalse :
      congressionalMentionUpgradesUnderlyingPressClaimToPrimaryTechnicalEvidence ≡ false

    formalisationTransfersExternalScientificAuthorshipToDASHI : Bool
    formalisationTransfersExternalScientificAuthorshipToDASHIIsFalse :
      formalisationTransfersExternalScientificAuthorshipToDASHI ≡ false

    namedInventorMayBeAttachedToPatentWhenPatentNamesInventor : Bool
    namedInventorMayBeAttachedToPatentWhenPatentNamesInventorIsTrue :
      namedInventorMayBeAttachedToPatentWhenPatentNamesInventor ≡ true

    namedAuthorMayBeAttachedToPublicationWhenPublicationNamesAuthor : Bool
    namedAuthorMayBeAttachedToPublicationWhenPublicationNamesAuthorIsTrue :
      namedAuthorMayBeAttachedToPublicationWhenPublicationNamesAuthor ≡ true

    namedPIOrLeadRequiresRoleSpecificReceipt : Bool
    namedPIOrLeadRequiresRoleSpecificReceiptIsTrue :
      namedPIOrLeadRequiresRoleSpecificReceipt ≡ true

canonicalScientificAttributionBoundary : ScientificAttributionBoundary
canonicalScientificAttributionBoundary =
  scientific-attribution-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- A small typed separation useful to downstream evidence hyperfabrics.
------------------------------------------------------------------------

record PersonWorkHypervoxel : Set where
  constructor person-work-hypervoxel
  field
    person : String
    work : String
    role : AttributionRole
    provenance : SourceStrength
    claimOwner : ClaimOwner

open PersonWorkHypervoxel public

fromAttribution : ScientificWorkAttribution → PersonWorkHypervoxel
fromAttribution a =
  person-work-hypervoxel
    (personName a)
    (scientificObject a)
    (attributionRole a)
    (sourceStrength a)
    (ownerOfClaim a)
