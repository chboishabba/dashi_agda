module DASHI.Cognition.CCDCOEP3Trumbo1996IndependentMediaBaselineExact where

------------------------------------------------------------------------
-- Original peer-reviewed content analysis, not GCC PR self-evaluation.
-- Craig Trumbo, Public Understanding of Science 5(3), 1996, 269-283.
-- DOI: 10.1088/0963-6625/5/3/006
-- SAGE publisher records a five-national-newspaper content study.
-- Publisher notes: FIRST HALF 1988 approx 400 column inches;
-- SECOND HALF 1989 approx 1200; FIRST HALF 1993 approx 350.
-- Published frame-coding reliability Scott pi = .78.
--
-- These three historical VOLUME windows are nonadjacent and pre/
-- around the uncertain Harrison launch date. They are NOT GCC-
-- attributed before/after frame shares, or a reader persuasion effect.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF

data PublishedHalfYear : Set where
  firstHalf1988 : PublishedHalfYear
  secondHalf1989 : PublishedHalfYear
  firstHalf1993 : PublishedHalfYear

approximateColumnInches : PublishedHalfYear → Nat
approximateColumnInches firstHalf1988 = 400
approximateColumnInches secondHalf1989 = 1200
approximateColumnInches firstHalf1993 = 350

data ObservedQuantity : Set where
  columnInchesOfClimateCoverage : ObservedQuantity
  frameIntercoderReliability : ObservedQuantity
  readerPersuasionEffect : ObservedQuantity
  GCCCausedCoverageDifference : ObservedQuantity

record IndependentMediaContentStudy : Set where
  constructor independentMediaContentStudy
  field
    selectedDOI : String
    journalArticleYear : Nat
    numberOfNationalNewspapers : Nat
    originalMicrodataReviewed : Bool
    sourceScopedFrameReliabilityNumerator : Nat
    sourceScopedFrameReliabilityDenominator : Nat
    sourceConfirmedGCCDeliveryTime : Bool
    independentGCCEffectMeasured : Bool

trumbo1996PublishedStudy : IndependentMediaContentStudy
trumbo1996PublishedStudy =
  independentMediaContentStudy
    "10.1088/0963-6625/5/3/006"
    1996
    5
    false
    78
    100
    false
    false

actualFiveNewspaperScope :
  IndependentMediaContentStudy.numberOfNationalNewspapers
    trumbo1996PublishedStudy ≡ 5
actualFiveNewspaperScope = refl

-- These are source reported *approximate* coverage magnitudes.
-- Exact arithmetic below merely checks transcription of summaries;
-- source uncertainty does NOT become an exact effect distribution.
reported1988Vs1993VolumeDifference :
  approximateColumnInches firstHalf1993 + 50
  ≡ approximateColumnInches firstHalf1988
reported1988Vs1993VolumeDifference = refl

reported1989Vs1993VolumeDifference :
  approximateColumnInches firstHalf1993 + 850
  ≡ approximateColumnInches secondHalf1989
reported1989Vs1993VolumeDifference = refl

reportedScottPiTimes100 :
  IndependentMediaContentStudy.sourceScopedFrameReliabilityNumerator
    trumbo1996PublishedStudy ≡ 78
reportedScottPiTimes100 = refl

independentBaselineDoesNotReportGCCEffect :
  IndependentMediaContentStudy.independentGCCEffectMeasured
    trumbo1996PublishedStudy ≡ false
independentBaselineDoesNotReportGCCEffect = refl

-- The same independent newspaper source volumes could coexist with
-- distinct hypotheses about who caused later media framing. A
-- coverage-volume chart cannot determine GCC's campaign-specific
-- causal contribution from itself.
data CausalHypothesisWorld : Set where
  backgroundIssueAttentionOnly : CausalHypothesisWorld
  backgroundAndGCCImpact : CausalHypothesisWorld

data CausalExplanation : Set where
  baselineWithNoGCCEffectIdentified : CausalExplanation
  additionalGCCEffectEstablished : CausalExplanation

sameReportedBaseline : CausalHypothesisWorld → Nat
sameReportedBaseline _ = approximateColumnInches firstHalf1993

differentUnobservedExplanations : CausalHypothesisWorld → CausalExplanation
differentUnobservedExplanations backgroundIssueAttentionOnly =
  baselineWithNoGCCEffectIdentified
differentUnobservedExplanations backgroundAndGCCImpact =
  additionalGCCEffectEstablished

independentVolumeDoesNotIdentifyAgencyCausality :
  NF.FactorsThrough sameReportedBaseline differentUnobservedExplanations → ⊥
independentVolumeDoesNotIdentifyAgencyCausality =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      backgroundIssueAttentionOnly backgroundAndGCCImpact
      refl (λ ()))

-- Preserve the original paper's source/frames distinctions:
-- scientists often quoted in problem/cause frames; politicians and
-- special interests often in judgment/remedy frames. These are
-- empirical paper results, not person-specific blame predicates.
