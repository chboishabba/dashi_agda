module DASHI.Governance.BlackGirlsMatterStudyScopeExact where

-- Source: Crenshaw with Priscilla Ocen and Jyoti Nanda (2015),
-- Black Girls Matter, AAPF / CISPS.
-- Primary publisher PDF, printed pages 2, 9, 26, 45-46 and note 26.
-- This is a typed representation of *the report's own stated scope*,
-- not a replication of raw CRDC data, a nationwide random sample, or
-- a causal school-to-prison follow-up cohort.
-- Participants and interviewees are sources of situated evidence:
-- they are not automatically the report's named authors.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

data EvidenceLayer : Set where
  districtAdministrativeData participantFocusGroup
  adultStakeholderInterview reportSynthesis : EvidenceLayer

data DomainClaim : Set where
  raceGenderDistrictDiscipline
  participantReportedSchoolExperience
  stakeholderReportedInstitutionalPractice
  nationalRepresentativeness
  disabilitySpecificDiscipline
  limitedEnglishProficiencyDiscipline
  individualCustodyTrajectory : DomainClaim

data Supports : EvidenceLayer → DomainClaim → Set where
  districtDataSupportsDistrictComparison :
    Supports districtAdministrativeData raceGenderDistrictDiscipline
  participantsSupportReportedExperience :
    Supports participantFocusGroup participantReportedSchoolExperience
  stakeholdersSupportReportedPractice :
    Supports adultStakeholderInterview stakeholderReportedInstitutionalPractice

districtDataDoesNotPayParticipantTestimony :
  Supports districtAdministrativeData participantReportedSchoolExperience → ⊥
districtDataDoesNotPayParticipantTestimony ()

focusGroupDoesNotPayNationalRepresentativeness :
  Supports participantFocusGroup nationalRepresentativeness → ⊥
focusGroupDoesNotPayNationalRepresentativeness ()

focusGroupDoesNotPayIndividualCustodyTrace :
  Supports participantFocusGroup individualCustodyTrajectory → ⊥
focusGroupDoesNotPayIndividualCustodyTrace ()

districtAnalysisDoesNotPayDisabilitySpecificClaim :
  Supports districtAdministrativeData disabilitySpecificDiscipline → ⊥
districtAnalysisDoesNotPayDisabilitySpecificClaim ()

districtAnalysisDoesNotPayLEPClaim :
  Supports districtAdministrativeData
    limitedEnglishProficiencyDiscipline → ⊥
districtAnalysisDoesNotPayLEPClaim ()

-- These are REPORT-CLAIM metadata, not reproduced participant microdata.
data District : Set where
  boston nyc : District

data AnalysisYear : Set where
  academicYear2011To2012 : AnalysisYear

record ReportDataScope : Set where
  constructor report-data-scope
  field
    year : AnalysisYear
    dataReleaseYear : Nat
    fieldSiteOne : District
    fieldSiteTwo : District
    observedYoungWomen : Nat
    interviewedStakeholders : Nat
    appendixPage : Nat
    focusGroupPage : Nat
    hasNationalProbabilitySample : Bool
    disabilityDisciplineAnalysed : Bool
    lepDisciplineAnalysed : Bool

reportStatedScope : ReportDataScope
reportStatedScope =
  report-data-scope
    academicYear2011To2012
    2014 boston nyc
    20 15
    45 26
    false false false

twentyYoungWomenReported :
  ReportDataScope.observedYoungWomen reportStatedScope ≡ 20
twentyYoungWomenReported = refl

fifteenStakeholdersReported :
  ReportDataScope.interviewedStakeholders reportStatedScope ≡ 15
fifteenStakeholdersReported = refl

disabilityAndLEPExcludedFromReportedDisciplineAnalysis :
  (ReportDataScope.disabilityDisciplineAnalysed reportStatedScope ≡ false)
  × (ReportDataScope.lepDisciplineAnalysed reportStatedScope ≡ false)
disabilityAndLEPExcludedFromReportedDisciplineAnalysis =
  refl , refl

focusGroupNotNationallyRepresentative :
  ReportDataScope.hasNationalProbabilitySample reportStatedScope ≡ false
focusGroupNotNationallyRepresentative = refl

-- Source-specific *claim* adequacy, not an empirical population estimator.
data ReportQuestion : Set where
  studyDescribedItsDistrictScope
  studyDescribedDisabilityDiscipline
  studyReportedIndividualCustodyOutcome : ReportQuestion

data SourceScopeStatus : Set where
  studied notStudied : SourceScopeStatus

scopeAnswer : ReportQuestion → SourceScopeStatus
scopeAnswer studyDescribedItsDistrictScope = studied
scopeAnswer studyDescribedDisabilityDiscipline = notStudied
scopeAnswer studyReportedIndividualCustodyOutcome = notStudied

disabledDisciplineWasNotPartOfAnalysedReportScope :
  scopeAnswer studyDescribedDisabilityDiscipline ≡ notStudied
disabledDisciplineWasNotPartOfAnalysedReportScope = refl

custodialTrajectoryWasNotTrackedAsAnIndividualOutcome :
  scopeAnswer studyReportedIndividualCustodyOutcome ≡ notStudied
custodialTrajectoryWasNotTrackedAsAnIndividualOutcome = refl

-- The claim that a dimension was *not studied* is not the claim that
-- the underlying harm was *absent*. A separate data collector is needed.
data UnmeasuredDisabilityWorld : Set where
  unreportedDisabilityHarm noDisabilityHarm : UnmeasuredDisabilityWorld

availableDisabilityResult : UnmeasuredDisabilityWorld → SourceScopeStatus
availableDisabilityResult _ = notStudied

actualDisabilityHarm : UnmeasuredDisabilityWorld → Bool
actualDisabilityHarm unreportedDisabilityHarm = true
actualDisabilityHarm noDisabilityHarm = false

notStudiedDoesNotMeanNoDisabilityHarm :
  INF.NonFactorabilityWitness
    availableDisabilityResult actualDisabilityHarm
notStudiedDoesNotMeanNoDisabilityHarm =
  INF.nonFactorabilityWitness
    unreportedDisabilityHarm noDisabilityHarm refl (λ ())

reportScopeCannotDecideUnstudiedHarm :
  INF.FactorsThrough
    availableDisabilityResult actualDisabilityHarm → ⊥
reportScopeCannotDecideUnstudiedHarm =
  INF.witnessRulesOutEveryFlatFactorisation
    notStudiedDoesNotMeanNoDisabilityHarm
