module DASHI.Culture.HouseOversightScientistRosterScopeExact where

------------------------------------------------------------------------
-- HOUSE OVERSIGHT SCIENTIST-ROSTER SCOPE / ATTRIBUTION BOUNDARY
--
-- Primary source:
-- U.S. House Committee on Oversight and Government Reform,
-- letter to the U.S. Department of Energy, 20 April 2026.
--
-- The letter says the Committee is investigating unconfirmed public reporting
-- concerning at least ten people connected to sensitive scientific information.
-- It explicitly names Michael David Hicks, Monica Reza, and William Neil
-- McCasland.  It then describes further people by institutional/category
-- membership.  Therefore a later article that supplies names for those
-- categories is a new attribution coordinate; those names may not be rewritten
-- as people explicitly named by Congress.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- Scope carriers.
------------------------------------------------------------------------

data CommitteeNamingStatus : Set where
  explicitlyNamedByCommittee
  categoryOnlyInCommitteeLetter
  suppliedByLaterReporting
  notInCommitteeLetter
  : CommitteeNamingStatus

record CommitteeRosterEntry : Set where
  constructor committee-roster-entry
  field
    personOrCategory : String
    namingStatus : CommitteeNamingStatus
    sourceStrength : Attribution.SourceStrength
    sourceLocator : String
    boundedReading : String

open CommitteeRosterEntry public

hicksCommitteeEntry : CommitteeRosterEntry
hicksCommitteeEntry =
  committee-roster-entry
    "Michael David Hicks"
    explicitlyNamedByCommittee
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026, page 1"
    "The Committee explicitly names Hicks while characterising the inquiry as based on unconfirmed public reporting."

rezaCommitteeEntry : CommitteeRosterEntry
rezaCommitteeEntry =
  committee-roster-entry
    "Monica Reza"
    explicitlyNamedByCommittee
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026, page 1"
    "The Committee explicitly names Reza; this receipt establishes committee naming, not every underlying technical or relationship allegation."

mccaslandCommitteeEntry : CommitteeRosterEntry
mccaslandCommitteeEntry =
  committee-roster-entry
    "William Neil McCasland"
    explicitlyNamedByCommittee
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026, page 1"
    "The Committee explicitly names McCasland; the separate alleged Reza relationship remains attributed to the public reports cited by the letter."

additionalJPLCategory : CommitteeRosterEntry
additionalJPLCategory =
  committee-roster-entry
    "two additional people affiliated with NASA Jet Propulsion Laboratory"
    categoryOnlyInCommitteeLetter
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026"
    "The committee letter supplies a category/count, not names in the text relied on here."

additionalLANLCategory : CommitteeRosterEntry
additionalLANLCategory =
  committee-roster-entry
    "two people affiliated with Los Alamos National Laboratory"
    categoryOnlyInCommitteeLetter
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026"
    "The committee letter supplies a category/count; any later name assignment requires a separate source receipt."

mitFusionCategory : CommitteeRosterEntry
mitFusionCategory =
  committee-roster-entry
    "an MIT scientist working on nuclear fusion"
    categoryOnlyInCommitteeLetter
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026"
    "The category is committee-primary; attaching a specific name requires a separate same-object/source weld."

pharmaceuticalResearcherCategory : CommitteeRosterEntry
pharmaceuticalResearcherCategory =
  committee-roster-entry
    "a pharmaceutical researcher"
    categoryOnlyInCommitteeLetter
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026"
    "The category is committee-primary; later identification of a person is not rewritten as explicit committee naming."

nuclearComponentContractorCategory : CommitteeRosterEntry
nuclearComponentContractorCategory =
  committee-roster-entry
    "a government contractor at a nuclear-weapons-component production facility"
    categoryOnlyInCommitteeLetter
    Attribution.primaryInstitutionalRecord
    "House Oversight letter to DOE, 20 April 2026"
    "The committee supplies the role/category only; a named-person match requires independent provenance."

------------------------------------------------------------------------
-- Explicit anti-laundering boundary.
------------------------------------------------------------------------

record CommitteeRosterScopeBoundary : Set where
  constructor committee-roster-scope-boundary
  field
    committeeInquiryExists : Bool
    committeeInquiryExistsIsTrue : committeeInquiryExists ≡ true

    committeeLetterSaysAtLeastTen : Bool
    committeeLetterSaysAtLeastTenIsTrue : committeeLetterSaysAtLeastTen ≡ true

    allAtLeastTenExplicitlyNamedInLetter : Bool
    allAtLeastTenExplicitlyNamedInLetterIsFalse :
      allAtLeastTenExplicitlyNamedInLetter ≡ false

    laterReporterNameBecomesCommitteePrimaryName : Bool
    laterReporterNameBecomesCommitteePrimaryNameIsFalse :
      laterReporterNameBecomesCommitteePrimaryName ≡ false

    committeeRepetitionMakesUnderlyingPublicReportPrimaryEvidence : Bool
    committeeRepetitionMakesUnderlyingPublicReportPrimaryEvidenceIsFalse :
      committeeRepetitionMakesUnderlyingPublicReportPrimaryEvidence ≡ false

    categoryMatchRequiresSameObjectReceipt : Bool
    categoryMatchRequiresSameObjectReceiptIsTrue :
      categoryMatchRequiresSameObjectReceipt ≡ true

    committeeInquiryImpliesCasesAreCausallyConnected : Bool
    committeeInquiryImpliesCasesAreCausallyConnectedIsFalse :
      committeeInquiryImpliesCasesAreCausallyConnected ≡ false

canonicalCommitteeRosterScopeBoundary : CommitteeRosterScopeBoundary
canonicalCommitteeRosterScopeBoundary =
  committee-roster-scope-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
