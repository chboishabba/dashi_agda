module DASHI.Culture.AmyEskridgeVideoRosterScopeWeldExact where

-- Exact cardinality/scoping cut for "she is the 11th person" at 00:21.
-- Sources:
-- U.S. House Oversight, Comer & Burlison letter 2026-04-20,
-- https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf
-- House says AT LEAST TEN in UNCONFIRMED media reporting, not an audited
-- total and not an exact eleven-scientist classification.
-- Amy Eskridge, family obituary, June 2022, as independently source-
-- inspected and recorded by AmyEskridgeDemiseCircumstancesSnowballExact.
-- See Docs/SourceAttributionPolicy.md. The arithmetic is DASHI-native;
-- it does not establish roster identity or video-author sourcing.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact as House
import DASHI.Culture.MissingDeceasedTwentyScientistRound11SourceReplayParetoExact as Research
import DASHI.Culture.MissingDeceasedRosterScopeReconciliationExact as Scope
import DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact as Amy
import DASHI.Culture.AmyEskridgeVideoSourceRegistryExact as Source

houseReportingCount : Nat
houseReportingCount = House.officialReportingCohortCount

retainedResearchCount : Nat
retainedResearchCount = Research.round11ScientificCohortCount

houseRetainedOverlap : Nat
houseRetainedOverlap = House.retainedTwentyOverlapCount

houseOutsideResearch : Nat
houseOutsideResearch = House.outsideRetainedTwentyCount

-- These finite equalities use the existing reported/reconstructed cohort
-- counts as inputs; they do not verify each person's external case record.
houseCountIsTen : houseReportingCount ≡ 10
houseCountIsTen = refl

researchCountIsTwenty : retainedResearchCount ≡ 20
researchCountIsTwenty = refl

overlapIsEight : houseRetainedOverlap ≡ 8
overlapIsEight = refl

housePartitionCheck : houseRetainedOverlap + houseOutsideResearch ≡ houseReportingCount
housePartitionCheck = refl

-- Arithmetic possibility is not provenance: there is no entitlement to
-- insert Amy as a House/reporting eleventh on this arithmetic alone.
candidateTenPlusAmy : Nat
candidateTenPlusAmy = houseReportingCount + 1

candidateNumeralIsEleven : candidateTenPlusAmy ≡ 11
candidateNumeralIsEleven = refl

-- Set-union count conditional on the exact Round44 eight-of-ten roster
-- overlap; not a count of scientists or a cohort common-cause proof.
conditionalUnionSize : Nat
conditionalUnionSize = retainedResearchCount + houseOutsideResearch

conditionalUnionIsTwentyTwo : conditionalUnionSize ≡ 22
conditionalUnionIsTwentyTwo = refl

record VideoElevenScopeAudit : Set where
  constructor video-eleven-scope-audit
  field
    houseRecord : Scope.ScopeReceipt
    originalHouseInquiry : House.OfficialInquiryPerson
    amyDeathRecord : Amy.DemiseSnowballAtom
    primaryHouseCarrier : Source.ScopedSource
    narratorNumber : Nat
    namedElevenMembershipInspected : Bool
    videoRosterEqualsHousePlusAmyPaid : Bool
    commonProgrammePaid : Bool
    workLinkedHarmPaid : Bool

videoElevenScopeAudit : VideoElevenScopeAudit
videoElevenScopeAudit = video-eleven-scope-audit
  Scope.houseInquiryScope House.hicks Amy.familyObituaryDateAtom
  Source.houseApril2026
  11 false false false false

-- Cannot infer a unique eleven-person roster merely from 10 + 1 = 11.
data ProvedVideoElevenEqualsHouseTenPlusAmy : Set where
data ProvedElevenAllScientists : Set where
data ProvedAllElevenShareHarmCause : Set where

noHouseToVideoMembershipShortcut : ProvedVideoElevenEqualsHouseTenPlusAmy → ⊥
noHouseToVideoMembershipShortcut ()

noRolePromotion : ProvedElevenAllScientists → ⊥
noRolePromotion ()

noCausalPromotion : ProvedAllElevenShareHarmCause → ⊥
noCausalPromotion ()
