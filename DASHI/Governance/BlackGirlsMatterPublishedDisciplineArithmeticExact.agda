module DASHI.Governance.BlackGirlsMatterPublishedDisciplineArithmeticExact where

-- DASHI arithmetic verification of PUBLISHED SUMMARY FIGURES, not original
-- US Department of Education CRDC row reconstruction or causal inference.
-- Original study: Kimberle W Crenshaw, with Priscilla Ocen and Jyoti Nanda,
-- Black Girls Matter (2015), pp. 19-21 and appendix p.45.
-- Report-text source: Columbia Law School posted PDF, 2021-05 manifestation.
-- Times/units must remain explicit: school discipline cases are not
-- individual students, relative risks or future custody outcomes.
open import DASHI.Core.Prelude

data District : Set where boston newYorkCity : District
data ReportedGroup : Set where
  blackGirls whiteGirls blackBoys whiteBoys : ReportedGroup

disciplineCases : District → ReportedGroup → Nat
disciplineCases boston blackGirls = 340
disciplineCases boston whiteGirls = 30
disciplineCases boston blackBoys = 637
disciplineCases boston whiteBoys = 81
disciplineCases newYorkCity blackGirls = 9076
disciplineCases newYorkCity whiteGirls = 884
disciplineCases newYorkCity blackBoys = 13823
disciplineCases newYorkCity whiteBoys = 2541

-- These equations prove integer multipliers and remainders of reported
-- numbers. They are not risk ratios (enrolment denominators unavailable).
bostonGirlsCasesElevenfoldPlusTen :
  disciplineCases boston blackGirls ≡
    11 * disciplineCases boston whiteGirls + 10
bostonGirlsCasesElevenfoldPlusTen = refl

newYorkGirlsCasesTenfoldPlus236 :
  disciplineCases newYorkCity blackGirls ≡
    10 * disciplineCases newYorkCity whiteGirls + 236
newYorkGirlsCasesTenfoldPlus236 = refl

bostonBoysCasesSevenfoldPlus70 :
  disciplineCases boston blackBoys ≡
    7 * disciplineCases boston whiteBoys + 70
bostonBoysCasesSevenfoldPlus70 = refl

newYorkBoysCasesFivefoldPlus1118 :
  disciplineCases newYorkCity blackBoys ≡
    5 * disciplineCases newYorkCity whiteBoys + 1118
newYorkBoysCasesFivefoldPlus1118 = refl

-- Figure 3/4: ROUNDED percentage shares within girls' district
-- enrollment and discipline distributions. Keep these distinct from
-- counts and from school-year-shifted all-students Table 1.
data MeasuredShare : Set where
  femaleEnrollmentShare femaleDisciplineShare : MeasuredShare

reportedRoundedPercent :
  District → MeasuredShare → ReportedGroup → Nat
reportedRoundedPercent boston femaleEnrollmentShare blackGirls = 28
reportedRoundedPercent boston femaleEnrollmentShare whiteGirls = 15
reportedRoundedPercent boston femaleEnrollmentShare blackBoys = 0
reportedRoundedPercent boston femaleEnrollmentShare whiteBoys = 0
reportedRoundedPercent boston femaleDisciplineShare blackGirls = 61
reportedRoundedPercent boston femaleDisciplineShare whiteGirls = 5
reportedRoundedPercent boston femaleDisciplineShare blackBoys = 0
reportedRoundedPercent boston femaleDisciplineShare whiteBoys = 0
reportedRoundedPercent newYorkCity femaleEnrollmentShare blackGirls = 34
reportedRoundedPercent newYorkCity femaleEnrollmentShare whiteGirls = 13
reportedRoundedPercent newYorkCity femaleEnrollmentShare blackBoys = 0
reportedRoundedPercent newYorkCity femaleEnrollmentShare whiteBoys = 0
reportedRoundedPercent newYorkCity femaleDisciplineShare blackGirls = 56
reportedRoundedPercent newYorkCity femaleDisciplineShare whiteGirls = 5
reportedRoundedPercent newYorkCity femaleDisciplineShare blackBoys = 0
reportedRoundedPercent newYorkCity femaleDisciplineShare whiteBoys = 0

-- Cross-product comparisons of ROUNDED within-girl shares. They do
-- NOT prove exact suspension probabilities or individual risks.
bostonFemaleShareCrossProductGap :
  reportedRoundedPercent boston femaleDisciplineShare blackGirls *
  reportedRoundedPercent boston femaleEnrollmentShare whiteGirls ≡
  reportedRoundedPercent boston femaleDisciplineShare whiteGirls *
  reportedRoundedPercent boston femaleEnrollmentShare blackGirls + 775
bostonFemaleShareCrossProductGap = refl

newYorkFemaleShareCrossProductGap :
  reportedRoundedPercent newYorkCity femaleDisciplineShare blackGirls *
  reportedRoundedPercent newYorkCity femaleEnrollmentShare whiteGirls ≡
  reportedRoundedPercent newYorkCity femaleDisciplineShare whiteGirls *
  reportedRoundedPercent newYorkCity femaleEnrollmentShare blackGirls + 558
newYorkFemaleShareCrossProductGap = refl

-- Table 1 explicitly cites a DIFFERENT year (2013-14) than the discipline
-- distribution (2011-12). No equality of population/time denominators
-- is licensed by the report alone.
data SourcePeriod : Set where
  discipline2011To2012 enrollmentTable2013To2014 : SourcePeriod

tableOnePeriod : SourcePeriod
tableOnePeriod = enrollmentTable2013To2014

disciplineFigurePeriod : SourcePeriod
disciplineFigurePeriod = discipline2011To2012

tableOneIsNotDisciplineFigurePeriod :
  tableOnePeriod ≡ disciplineFigurePeriod → ⊥
tableOneIsNotDisciplineFigurePeriod ()

-- Never promote the reported figure into an authenticated original
-- administrative row. That requires the separate original CRDC source.
record OriginalCRDCWeld (OriginalRow : Set) : Set₁ where
  field
    originalRow : District → ReportedGroup → OriginalRow
    rowIsOfficialCRDC : OriginalRow → Set
    schoolYearAndIndicatorAligned : OriginalRow → Set
    numeratorDefinitionAudited : OriginalRow → Set
    populationDenominatorAudited : OriginalRow → Set
