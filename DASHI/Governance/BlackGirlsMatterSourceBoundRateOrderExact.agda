module DASHI.Governance.BlackGirlsMatterSourceBoundRateOrderExact where

-- Conditional source-paid comparison for actual 2011-12 OCR rows.
-- Mathematical owner DASHI. Federal data owner: US DOE OCR.
-- Study interpretation owner: Crenshaw with Ocen and Nanda (2015).
-- No federal rows or original-file digest are supplied by this module.

open import DASHI.Core.Prelude
import DASHI.Governance.BlackGirlsMatterCRDCOriginalRowAdmissionExact as OCR
import DASHI.Governance.BlackGirlsMatterDenominatorSensitivityExact as Sensitivity
import DASHI.Core.IntersectionalNonFactorability as INF

-- This structure inherits year, district, group, disability eligibility,
-- measure, observed values, unique-person units and positive enrollments.
-- The comparison is a strict exact cross-product property, without rounding.
record CertifiedBlackHigher
    (src : OCR.VerifiedCRDCSource)
    (d : OCR.District)
    (eligibility : OCR.DisabilityScope)
    (measure : OCR.Measure) : Set where
  constructor certified-black-higher
  field
    comparable : OCR.ComparableRatePair src d eligibility measure
    blackTimesWhitePopulation : Nat
    whiteTimesBlackPopulation : Nat
    blackCrossProduct :
      blackTimesWhitePopulation ≡
        OCR.numerator (OCR.blackGirlsRate comparable) *
        OCR.denominator (OCR.whiteGirlsRate comparable)
    whiteCrossProduct :
      whiteTimesBlackPopulation ≡
        OCR.numerator (OCR.whiteGirlsRate comparable) *
        OCR.denominator (OCR.blackGirlsRate comparable)
    strictlyLarger : whiteTimesBlackPopulation < blackTimesWhitePopulation

open CertifiedBlackHigher public

-- No hypothesis is manufactured here: a genuinely source-paid pair and
-- a comparison proof must be supplied by a caller.
certifiedHigherRequiresSamePopulationRows :
  ∀ {src : OCR.VerifiedCRDCSource}
    {d : OCR.District}
    {e : OCR.DisabilityScope}
    {m : OCR.Measure} →
  CertifiedBlackHigher src d e m →
  OCR.ComparableRatePair src d e m
certifiedHigherRequiresSamePopulationRows = comparable

-- A caller cannot turn a differently indexed disability population
-- into the selected one by definitional equality.
eligibilityMismatchCannotPayRate :
  OCR.studentsWithoutDisabilities ≡ OCR.allStudents → ⊥
eligibilityMismatchCannotPayRate =
  OCR.differentDisabilityEligibilityIsNotSamePopulation

-- In particular the 340-vs-30 Boston *reported cases* cannot replace
-- population-aligned original OCR raw records or determine rate ordering.
publishedBostonCountsCannotChooseDirection :
  INF.FactorsThrough Sensitivity.observedCountPair
    Sensitivity.syntheticDirection → ⊥
publishedBostonCountsCannotChooseDirection =
  Sensitivity.caseCountsAloneDoNotDetermineRateOrder

-- The ratio comparison's legal/sociological significance is not contained
-- in the certificate: interpretation, inclusion criteria, causal selection,
-- disability/access provisions and material outcomes require fresh receipts.
