module DASHI.Governance.BlackGirlsMatterDenominatorSensitivityExact where

-- Original DASHI mathematical sensitivity countermodel.
-- The Black Girls Matter (2015) Boston *case counts* are 340/30.
-- The enrollment denominators below are SYNTHETIC, not OCR data,
-- not plausible enrollment claims, and not observed student risks.
-- No rate is defined from an actual CRDC source without source-matched
-- unique-person numerator and same-population denominator evidence.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.BlackGirlsMatterPublishedDisciplineArithmeticExact as Report

data SyntheticEnrollmentScenario : Set where
  blackHigherWhiteLower whiteHigherBlackLower : SyntheticEnrollmentScenario

-- Both scenarios share *the same actual published report counts*.
blackCases : SyntheticEnrollmentScenario → Nat
blackCases _ =
  Report.disciplineCases Report.boston Report.blackGirls

whiteCases : SyntheticEnrollmentScenario → Nat
whiteCases _ =
  Report.disciplineCases Report.boston Report.whiteGirls

-- Example denominators are deliberately hypothetical, and above
-- corresponding numerators, solely to demonstrate order reversal.
blackEnrollment : SyntheticEnrollmentScenario → Nat
blackEnrollment blackHigherWhiteLower = 3400
blackEnrollment whiteHigherBlackLower = 34000

whiteEnrollment : SyntheticEnrollmentScenario → Nat
whiteEnrollment blackHigherWhiteLower = 3000
whiteEnrollment whiteHigherBlackLower = 300

observedCountPair : SyntheticEnrollmentScenario → Nat × Nat
observedCountPair s = blackCases s , whiteCases s

-- For positive denominators, the relative ordering of b/B and w/W
-- is characterized by b*W versus w*B. There is no rounding here.
blackCrossProduct : SyntheticEnrollmentScenario → Nat
blackCrossProduct s = blackCases s * whiteEnrollment s

whiteCrossProduct : SyntheticEnrollmentScenario → Nat
whiteCrossProduct s = whiteCases s * blackEnrollment s

data RateDirection : Set where
  blackRateHigher whiteRateHigher : RateDirection

-- Finite certificate: each direction is backed by exact arithmetic.
-- A structural constructor does NOT certify a real district's rates.
syntheticDirection : SyntheticEnrollmentScenario → RateDirection
syntheticDirection blackHigherWhiteLower = blackRateHigher
syntheticDirection whiteHigherBlackLower = whiteRateHigher

blackHigherNumeratorCrossProduct :
  blackCrossProduct blackHigherWhiteLower ≡ 1020000
blackHigherNumeratorCrossProduct = refl

blackHigherComparatorCrossProduct :
  whiteCrossProduct blackHigherWhiteLower ≡ 102000
blackHigherComparatorCrossProduct = refl

whiteHigherNumeratorCrossProduct :
  blackCrossProduct whiteHigherBlackLower ≡ 102000
whiteHigherNumeratorCrossProduct = refl

whiteHigherComparatorCrossProduct :
  whiteCrossProduct whiteHigherBlackLower ≡ 1020000
whiteHigherComparatorCrossProduct = refl

publishedCountsUnchanged :
  observedCountPair blackHigherWhiteLower
  ≡ observedCountPair whiteHigherBlackLower
publishedCountsUnchanged = refl

denominatorsChangeRateDirection :
  INF.NonFactorabilityWitness observedCountPair syntheticDirection
denominatorsChangeRateDirection =
  INF.nonFactorabilityWitness
    blackHigherWhiteLower whiteHigherBlackLower
    refl (λ ())

caseCountsAloneDoNotDetermineRateOrder :
  INF.FactorsThrough observedCountPair syntheticDirection → ⊥
caseCountsAloneDoNotDetermineRateOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    denominatorsChangeRateDirection

-- Exact arithmetic certificates accompany the two synthetic scenarios,
-- preventing a status flag being mistaken for empirically measured data.
record SyntheticCrossProductWitness : Set where
  constructor synthetic-cross-product-witness
  field
    firstLeft : blackCrossProduct blackHigherWhiteLower ≡ 1020000
    firstRight : whiteCrossProduct blackHigherWhiteLower ≡ 102000
    secondLeft : blackCrossProduct whiteHigherBlackLower ≡ 102000
    secondRight : whiteCrossProduct whiteHigherBlackLower ≡ 1020000

syntheticCrossProductWitness : SyntheticCrossProductWitness
syntheticCrossProductWitness =
  synthetic-cross-product-witness refl refl refl refl
