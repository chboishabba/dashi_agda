module DASHI.Education.RelationalEducationGateAlgebra where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Primitive using (Set)

------------------------------------------------------------------------
-- Seven-gate education relation and exact overlap-frame arithmetic.

data EducationGate : Set where
  voiceGate : EducationGate
  agencyGate : EducationGate
  situatedEthicsGate : EducationGate
  partnershipGate : EducationGate
  enactmentGate : EducationGate
  engagementIntelligenceGate : EducationGate
  equityConditionsGate : EducationGate

canonicalEducationGates : List EducationGate
canonicalEducationGates =
  voiceGate ∷ agencyGate ∷ situatedEthicsGate ∷ partnershipGate
  ∷ enactmentGate ∷ engagementIntelligenceGate ∷ equityConditionsGate ∷ []

record EducationRelation : Set₁ where
  field
    Voice : Set
    Agency : Set
    SituatedEthics : Set
    Partnership : Set
    Enactment : Set
    EngagementIntelligence : Set
    EquityConditions : Set

record ValidEducationRelation (E : EducationRelation) : Set where
  field
    voice : EducationRelation.Voice E
    agency : EducationRelation.Agency E
    situatedEthics : EducationRelation.SituatedEthics E
    partnership : EducationRelation.Partnership E
    enactment : EducationRelation.Enactment E
    engagementIntelligence : EducationRelation.EngagementIntelligence E
    equityConditions : EducationRelation.EquityConditions E

record EducationMetricGovernance : Set where
  constructor mkEducationMetricGovernance
  field
    surveyEqualsVoice : Bool
    surveyEqualsVoiceIsFalse : surveyEqualsVoice ≡ false
    clickEqualsLearning : Bool
    clickEqualsLearningIsFalse : clickEqualsLearning ≡ false
    attendanceEqualsEngagement : Bool
    attendanceEqualsEngagementIsFalse : attendanceEqualsEngagement ≡ false
    accessEqualsEquity : Bool
    accessEqualsEquityIsFalse : accessEqualsEquity ≡ false
    trainingEqualsEnactment : Bool
    trainingEqualsEnactmentIsFalse : trainingEqualsEnactment ≡ false

canonicalEducationMetricGovernance : EducationMetricGovernance
canonicalEducationMetricGovernance =
  mkEducationMetricGovernance false refl false refl false refl false refl false refl

record FiniteRate : Set where
  constructor rate
  field
    numerator : Nat
    denominator : Nat

multiplyRate : FiniteRate → FiniteRate → FiniteRate
multiplyRate (rate a m) (rate b n) = rate (a * b) (m * n)

threePerHundred : FiniteRate
threePerHundred = rate 3 100

sevenPerHundred : FiniteRate
sevenPerHundred = rate 7 100

expectedIndependentOverlap : FiniteRate
expectedIndependentOverlap = multiplyRate threePerHundred sevenPerHundred

threeTimesSevenIsTwentyOne : 3 * 7 ≡ 21
threeTimesSevenIsTwentyOne = refl

hundredTimesHundredIsTenThousand : 100 * 100 ≡ 10000
hundredTimesHundredIsTenThousand = refl

expectedIndependentOverlapIsTwentyOnePerTenThousand :
  expectedIndependentOverlap ≡ rate 21 10000
expectedIndependentOverlapIsTwentyOnePerTenThousand = refl

record OverlapFrameSeparation : Set where
  constructor mkOverlapFrameSeparation
  field
    firstMarginal : FiniteRate
    secondMarginal : FiniteRate
    secondOrderOverlap : FiniteRate
    firstMarginalIsCanonical : firstMarginal ≡ threePerHundred
    secondMarginalIsCanonical : secondMarginal ≡ sevenPerHundred
    secondOrderOverlapIsCanonical : secondOrderOverlap ≡ expectedIndependentOverlap
    twentyOneIsFirstOrderPopulationCount : Bool
    twentyOneIsFirstOrderPopulationCountIsFalse :
      twentyOneIsFirstOrderPopulationCount ≡ false

canonicalOverlapFrameSeparation : OverlapFrameSeparation
canonicalOverlapFrameSeparation =
  mkOverlapFrameSeparation
    threePerHundred sevenPerHundred expectedIndependentOverlap
    refl refl refl false refl
