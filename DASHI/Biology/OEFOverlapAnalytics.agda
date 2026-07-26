module DASHI.Biology.OEFOverlapAnalytics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- First-, second-, and higher-order OEF overlap surfaces.
--
-- Overlap is retained as pedagogically meaningful evidence.  It is not
-- treated as classification failure, statistical independence proof,
-- causal effect, or universal engagement law.

data Never : Set where

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

_×N_ : Nat → Nat → Nat
zero ×N n = zero
suc m ×N n = n +N (m ×N n)

threeTimesSevenIsTwentyOne : 3 ×N 7 ≡ 21
threeTimesSevenIsTwentyOne = refl

hundredTimesHundredIsTenThousand : 100 ×N 100 ≡ 10000
hundredTimesHundredIsTenThousand = refl

data OverlapOrder : Set where
  firstOrder : OverlapOrder
  secondOrder : OverlapOrder
  thirdOrder : OverlapOrder
  higherOrder : OverlapOrder

data OverlapComparison : Set where
  belowIndependenceCandidate : OverlapComparison
  atIndependenceCandidate : OverlapComparison
  aboveIndependenceCandidate : OverlapComparison
  unresolvedOverlapCandidate : OverlapComparison

record OverlapObservation : Set where
  constructor mkOverlapObservation
  field
    observationLabel : String
    observationOrder : OverlapOrder
    leftElement : OEF.OEFElement
    rightElement : OEF.OEFElement
    optionalThirdElement : List OEF.OEFElement
    totalObservedComments : Nat
    leftObservedCount : Nat
    rightObservedCount : Nat
    jointObservedCount : Nat
    independentNumerator : Nat
    independentDenominator : Nat
    comparison : OverlapComparison
    overlapCandidateOnly : Bool
    overlapCandidateOnlyIsTrue : overlapCandidateOnly ≡ true
    overlapSignalNotNoise : Bool
    overlapSignalNotNoiseIsTrue : overlapSignalNotNoise ≡ true
    overlapNoCausalPromotion : Bool
    overlapNoCausalPromotionIsTrue : overlapNoCausalPromotion ≡ true
    overlapRequiresUncertainty : Bool
    overlapRequiresUncertaintyIsTrue : overlapRequiresUncertainty ≡ true
    notes : List String

open OverlapObservation public

canonicalForumOverlapObservation : OverlapObservation
canonicalForumOverlapObservation =
  mkOverlapObservation
    "forum cognitive-collaborative overlap candidate"
    secondOrder
    OEF.cognitiveEngagement
    OEF.collaborativeEngagement
    ( OEF.socialEngagement
    ∷ OEF.behaviouralEngagement
    ∷ [] )
    1
    1
    1
    1
    1
    1
    aboveIndependenceCandidate
    true refl
    true refl
    true refl
    true refl
    ( "The canonical forum statement inhabits cognitive, collaborative, social, and behavioural fibres."
    ∷ "The row witnesses multi-fibre membership, not a population estimate."
    ∷ [] )

record ChanceOverlapReceipt : Set where
  constructor mkChanceOverlapReceipt
  field
    receiptLabel : String
    leftNumerator : Nat
    leftDenominator : Nat
    rightNumerator : Nat
    rightDenominator : Nat
    jointNumerator : Nat
    jointDenominator : Nat
    jointNumeratorCorrect : jointNumerator ≡ leftNumerator ×N rightNumerator
    jointDenominatorCorrect : jointDenominator ≡ leftDenominator ×N rightDenominator
    noTwentyOnePercentCollapse : Bool
    noTwentyOnePercentCollapseIsTrue : noTwentyOnePercentCollapse ≡ true
    interpretation : String

open ChanceOverlapReceipt public

canonicalThreeSevenChanceOverlap : ChanceOverlapReceipt
canonicalThreeSevenChanceOverlap =
  mkChanceOverlapReceipt
    "three-percent by seven-percent chance-overlap receipt"
    3
    100
    7
    100
    21
    10000
    refl
    refl
    true
    refl
    "Three percent times seven percent is twenty-one per ten-thousand, not twenty-one percent; actual overlap must be compared with this independence baseline."

record OEFOverlapAnalytics : Set where
  constructor mkOEFOverlapAnalytics
  field
    sourceSystem : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceSystemIsCanonical : sourceSystem ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    canonicalObservation : OverlapObservation
    canonicalObservationIsCanonical : canonicalObservation ≡ canonicalForumOverlapObservation
    chanceOverlapReceipt : ChanceOverlapReceipt
    chanceOverlapReceiptIsCanonical : chanceOverlapReceipt ≡ canonicalThreeSevenChanceOverlap
    firstOrderInsufficient : Bool
    firstOrderInsufficientIsTrue : firstOrderInsufficient ≡ true
    secondOrderOverlapRequired : Bool
    secondOrderOverlapRequiredIsTrue : secondOrderOverlapRequired ≡ true
    overlapPreservesMultiFibreMeaning : Bool
    overlapPreservesMultiFibreMeaningIsTrue : overlapPreservesMultiFibreMeaning ≡ true
    overlapNotCausalEffect : Bool
    overlapNotCausalEffectIsTrue : overlapNotCausalEffect ≡ true
    reading : String

open OEFOverlapAnalytics public

canonicalOEFOverlapAnalytics : OEFOverlapAnalytics
canonicalOEFOverlapAnalytics =
  mkOEFOverlapAnalytics
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalForumOverlapObservation refl
    canonicalThreeSevenChanceOverlap refl
    true refl
    true refl
    true refl
    true refl
    "OEF engagement overlap is evidence-bearing: the relevant question is which fibres co-occur in the same comments, students, courses, and times, compared with an independence baseline and under uncertainty governance."

OverlapCarriesPedagogicalInformation : Set
OverlapCarriesPedagogicalInformation =
  overlapPreservesMultiFibreMeaning canonicalOEFOverlapAnalytics ≡ true

overlapCarriesPedagogicalInformation :
  OverlapCarriesPedagogicalInformation
overlapCarriesPedagogicalInformation =
  overlapPreservesMultiFibreMeaningIsTrue canonicalOEFOverlapAnalytics

data OverlapPromotionRoute : Set where
  candidateOverlapRoute : OverlapPromotionRoute
  overlapEqualsCausationRoute : OverlapPromotionRoute
  overlapEqualsStudentEssenceRoute : OverlapPromotionRoute
  firstOrderChartEqualsWholeEcologyRoute : OverlapPromotionRoute

AdmissibleOverlapPromotionRoute : OverlapPromotionRoute → Set
AdmissibleOverlapPromotionRoute candidateOverlapRoute = ⊤
AdmissibleOverlapPromotionRoute overlapEqualsCausationRoute = Never
AdmissibleOverlapPromotionRoute overlapEqualsStudentEssenceRoute = Never
AdmissibleOverlapPromotionRoute firstOrderChartEqualsWholeEcologyRoute = Never

overlapEqualsCausationBlocked :
  AdmissibleOverlapPromotionRoute overlapEqualsCausationRoute → Never
overlapEqualsCausationBlocked ()

overlapEqualsStudentEssenceBlocked :
  AdmissibleOverlapPromotionRoute overlapEqualsStudentEssenceRoute → Never
overlapEqualsStudentEssenceBlocked ()

firstOrderChartEqualsWholeEcologyBlocked :
  AdmissibleOverlapPromotionRoute firstOrderChartEqualsWholeEcologyRoute → Never
firstOrderChartEqualsWholeEcologyBlocked ()
