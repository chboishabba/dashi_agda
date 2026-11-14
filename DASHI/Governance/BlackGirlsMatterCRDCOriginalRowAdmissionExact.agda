module DASHI.Governance.BlackGirlsMatterCRDCOriginalRowAdmissionExact where

-- Source owner: US Department of Education, Office for Civil Rights,
-- CRDC 2011-12 survey/data definitions and public-use file.
-- Source interpretation: Crenshaw with Ocen/Nanda, Black Girls Matter (2015).
-- Mathematical proof/receipt owner: DASHI.
-- No original ZIP bytes/rows, verification hash, or administrative key
-- have been recovered. Thus this is an UNFILLED source-admission interface.
-- It does not make the published numbers a raw-data replication.

open import DASHI.Core.Prelude

data SchoolYear : Set where
  y2011to2012 y2013to2014 : SchoolYear

data District : Set where
  boston nyc : District

data Population : Set where
  blackGirls whiteGirls blackBoys whiteBoys : Population

data Measure : Set where
  schoolEnrollment
  oneOutOfSchoolSuspension
  multipleOutOfSchoolSuspensions
  inSchoolSuspension
  expulsionWithServices
  expulsionWithoutServices
  zeroToleranceExpulsion
  referralToLawEnforcement
  schoolRelatedArrest : Measure

data DisabilityScope : Set where
  allStudents studentsWithoutDisabilities studentsWithDisabilities : DisabilityScope

data CountingUnit : Set where
  uniqueStudents studentsPerIndicator disciplinaryEvents : CountingUnit

-- Source data cells MUST distinguish actual integer zero, nonzero reported
-- counts, suppressed values, and missing/not-collected values. Treating
-- suppression or missingness as zero changes the underlying proposition.
data ReportedCell : Set where
  observed : Nat → ReportedCell
  suppressed : ReportedCell
  notReported : ReportedCell

data OriginalFileManifest : Set where
  fileManifest : OriginalFileManifest

record VerifiedCRDCSource : Set₁ where
  field
    Row : Set
    officialManifest : OriginalFileManifest
    originalFileDigestVerified : Set
    originalSourceVersionVerified : Set
    sourceRow : SchoolYear → District → Population → Measure → Row
    sourceCell : Row → ReportedCell
    sourceCountingUnit : Row → CountingUnit
    sourceDisabilityScope : Row → DisabilityScope
    sourcePeriod : Row → SchoolYear
    sourceDistrict : Row → District
    sourcePopulation : Row → Population
    sourceMeasure : Row → Measure
    auditOriginalRow : Row → Set

open VerifiedCRDCSource public

-- If a source file has been obtained and checked, every selected value
-- requires the original row and SAME-YEAR/DISTRICT/GROUP/MEASURE identity.
record MatchedOriginalCell
  (src : VerifiedCRDCSource)
  (year : SchoolYear)
  (district : District)
  (group : Population)
  (eligibility : DisabilityScope)
  (measure : Measure) : Set where
  constructor matched-original-cell
  field
    originalDigest : originalFileDigestVerified src
    originalVersion : originalSourceVersionVerified src
    selectedRow : Row src
    rowAudit : auditOriginalRow src selectedRow
    periodMatches : sourcePeriod src selectedRow ≡ year
    districtMatches : sourceDistrict src selectedRow ≡ district
    groupMatches : sourcePopulation src selectedRow ≡ group
    eligibilityMatches : sourceDisabilityScope src selectedRow ≡ eligibility
    measureMatches : sourceMeasure src selectedRow ≡ measure

open MatchedOriginalCell public

differentDisabilityEligibilityIsNotSamePopulation :
  studentsWithoutDisabilities ≡ allStudents → ⊥
differentDisabilityEligibilityIsNotSamePopulation ()

-- A raw cell source alone does not establish a student denominator:
-- the counting unit is a separate required receipt.
record SamePopulationRateReceipt
  (src : VerifiedCRDCSource)
  (district : District)
  (group : Population)
  (eligibility : DisabilityScope)
  (measure : Measure) : Set where
  constructor same-population-rate-receipt
  field
    numeratorRow :
      MatchedOriginalCell src y2011to2012 district group eligibility measure
    denominatorRow :
      MatchedOriginalCell src y2011to2012 district group eligibility schoolEnrollment
    numerator : Nat
    denominator : Nat
    numeratorIsObserved :
      sourceCell src (selectedRow numeratorRow) ≡ observed numerator
    denominatorIsObserved :
      sourceCell src (selectedRow denominatorRow) ≡ observed denominator
    unitIsUniqueStudents :
      sourceCountingUnit src (selectedRow numeratorRow) ≡ uniqueStudents
    enrollmentIsUniqueStudents :
      sourceCountingUnit src (selectedRow denominatorRow) ≡ uniqueStudents
    positiveEnrollment : Nat
    denominatorNonzero : denominator ≡ suc positiveEnrollment

open SamePopulationRateReceipt public

-- Distinguish one vs repeated out-of-school suspension;
-- each is a DIFFERENT original CRDC indicator, not an episode duplicate.
oneAndRepeatedSuspensionAreDifferent :
  oneOutOfSchoolSuspension ≡ multipleOutOfSchoolSuspensions → ⊥
oneAndRepeatedSuspensionAreDifferent ()

-- Distinct years prevent the 2013-14 published enrollment summary from
-- serving as a 2011-12 matched enrollment receipt by definitional equality.
printedEnrollmentTableCannotReplaceOriginal2011Enrollment :
  y2013to2014 ≡ y2011to2012 → ⊥
printedEnrollmentTableCannotReplaceOriginal2011Enrollment ()

suppressedNotZero : suppressed ≡ observed 0 → ⊥
suppressedNotZero ()

missingNotZero : notReported ≡ observed 0 → ⊥
missingNotZero ()

-- Cross-population disparity requires TWO separately admitted same-year
-- denominators with the SAME measure, never merely two discipline counts.
record ComparableRatePair
  (src : VerifiedCRDCSource)
  (district : District)
  (eligibility : DisabilityScope)
  (measure : Measure) : Set where
  constructor comparable-rate-pair
  field
    blackGirlsRate :
      SamePopulationRateReceipt src district blackGirls eligibility measure
    whiteGirlsRate :
      SamePopulationRateReceipt src district whiteGirls eligibility measure

open ComparableRatePair public

-- A source-paid comparison can at most supply a finite count
-- cross-product. Interpretations of causality and dispositional motive
-- still require independent evidence and cannot be inferred from this.
comparableRateCrossProducts :
  (src : VerifiedCRDCSource)
  (district : District)
  (eligibility : DisabilityScope)
  (measure : Measure) →
  ComparableRatePair src district eligibility measure → Nat × Nat
comparableRateCrossProducts src district eligibility measure p =
  (numerator (blackGirlsRate p) * denominator (whiteGirlsRate p)) ,
  (numerator (whiteGirlsRate p) * denominator (blackGirlsRate p))

-- No canonical VerifiedCRDCSource or ComparableRatePair is inhabited
-- here: the original data and audit receipts are not present in-repo.
