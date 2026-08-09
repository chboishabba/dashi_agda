module DASHI.Biology.DirectedAttractorPortfolioCalculus where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TraumaMemoryAttractorPortfolio as Memory
import DASHI.Biology.DirectedPortfolioSourceAtlas as Sources

one<three : 1 < 3
one<three = s≤s (s≤s z≤n)

three<four : 3 < 4
three<four = s≤s (s≤s (s≤s (s≤s z≤n)))

four<twelve : 4 < 12
four<twelve = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

three<sixteen : 3 < 16
three<sixteen = s≤s (s≤s (s≤s (s≤s z≤n)))

two≤three : 2 ≤ 3
two≤three = s≤s (s≤s z≤n)

two≤four : 2 ≤ 4
two≤four = s≤s (s≤s z≤n)

three≤four : 3 ≤ 4
three≤four = s≤s (s≤s (s≤s z≤n))

zero<six : 0 < 6
zero<six = s≤s z≤n

threeNot≤one : ¬ (3 ≤ 1)
threeNot≤one ()

threeNot≤two : ¬ (3 ≤ 2)
threeNot≤two ()

record ResourceVector : Set where
  constructor resourceVector
  field
    attention money time emotional administrative legal social : Nat

open ResourceVector public

_⊕R_ : ResourceVector → ResourceVector → ResourceVector
x ⊕R y = resourceVector
  (attention x + attention y) (money x + money y) (time x + time y)
  (emotional x + emotional y) (administrative x + administrative y)
  (legal x + legal y) (social x + social y)

record ResourceWiseFits (demand capacity : ResourceVector) : Set where
  constructor resourceWiseFits
  field
    attentionFits : attention demand ≤ attention capacity
    moneyFits : money demand ≤ money capacity
    timeFits : time demand ≤ time capacity
    emotionalFits : emotional demand ≤ emotional capacity
    administrativeFits : administrative demand ≤ administrative capacity
    legalFits : legal demand ≤ legal capacity
    socialFits : social demand ≤ social capacity

unitDemand : ResourceVector
unitDemand = resourceVector 1 1 1 1 1 1 1

twoBranchDemand : ResourceVector
twoBranchDemand = unitDemand ⊕R unitDemand

canonicalCapacity : ResourceVector
canonicalCapacity = resourceVector 3 3 3 3 3 3 3

twoBranchDemandFitsCapacity : ResourceWiseFits twoBranchDemand canonicalCapacity
twoBranchDemandFitsCapacity = resourceWiseFits two≤three two≤three two≤three two≤three two≤three two≤three two≤three

record AttentionAllocation : Set where
  constructor attentionAllocation
  field allocatedAttention viabilityThreshold : Nat
        allocationReading : String

open AttentionAllocation public

ViableAllocation : AttentionAllocation → Set
ViableAllocation a = viabilityThreshold a ≤ allocatedAttention a

focusedAllocation : AttentionAllocation
focusedAllocation = attentionAllocation 4 3 "Focused flow crosses the branch viability threshold."

diffusedAllocation : AttentionAllocation
diffusedAllocation = attentionAllocation 2 3 "Aggregate capacity remains, but local flow falls below threshold."

focusedAllocationViable : ViableAllocation focusedAllocation
focusedAllocationViable = three≤four

diffusedAllocationNotViable : ¬ ViableAllocation diffusedAllocation
diffusedAllocationNotViable = threeNot≤two

record AggregateServiceableLocalFailure : Set where
  constructor aggregateServiceableLocalFailure
  field
    aggregateFits : ResourceWiseFits twoBranchDemand canonicalCapacity
    localFailure : ¬ ViableAllocation diffusedAllocation

canonicalAggregateServiceableLocalFailure : AggregateServiceableLocalFailure
canonicalAggregateServiceableLocalFailure = aggregateServiceableLocalFailure twoBranchDemandFitsCapacity diffusedAllocationNotViable

record DriftBalance : Set where
  constructor driftBalance
  field gain loss : Nat

open DriftBalance public

Toward : DriftBalance → Set
Toward d = loss d < gain d

Away : DriftBalance → Set
Away d = gain d < loss d

shortReliefDrift : DriftBalance
shortReliefDrift = driftBalance 3 1

longTrapDrift : DriftBalance
longTrapDrift = driftBalance 1 3

shortReliefMovesToward : Toward shortReliefDrift
shortReliefMovesToward = one<three

longHorizonMovesAway : Away longTrapDrift
longHorizonMovesAway = one<three

record AttractiveDeadEndWitness : Set where
  constructor attractiveDeadEndWitness
  field shortToward : Toward shortReliefDrift
        longAway : Away longTrapDrift
        captureRisk : Nat

canonicalAttractiveDeadEndWitness : AttractiveDeadEndWitness
canonicalAttractiveDeadEndWitness = attractiveDeadEndWitness shortReliefMovesToward longHorizonMovesAway 8

record AttractorDriftVector : Set where
  constructor attractorDriftVector
  field
    housingDrift safetyDrift autonomyDrift relationshipDrift justiceDrift healthDrift : DriftBalance

open AttractorDriftVector public

record AttractorWeights : Set where
  constructor attractorWeights
  field
    housingWeight safetyWeight autonomyWeight relationshipWeight justiceWeight healthWeight : Nat

open AttractorWeights public

weightedGain : AttractorWeights → AttractorDriftVector → Nat
weightedGain w d =
  housingWeight w * gain (housingDrift d) + safetyWeight w * gain (safetyDrift d)
  + autonomyWeight w * gain (autonomyDrift d) + relationshipWeight w * gain (relationshipDrift d)
  + justiceWeight w * gain (justiceDrift d) + healthWeight w * gain (healthDrift d)

weightedLoss : AttractorWeights → AttractorDriftVector → Nat
weightedLoss w d =
  housingWeight w * loss (housingDrift d) + safetyWeight w * loss (safetyDrift d)
  + autonomyWeight w * loss (autonomyDrift d) + relationshipWeight w * loss (relationshipDrift d)
  + justiceWeight w * loss (justiceDrift d) + healthWeight w * loss (healthDrift d)

interventionAutonomyTradeoff : AttractorDriftVector
interventionAutonomyTradeoff = attractorDriftVector
  (driftBalance 0 0) (driftBalance 3 0) (driftBalance 0 4)
  (driftBalance 0 0) (driftBalance 0 0) (driftBalance 0 0)

safetyPriorityWeights : AttractorWeights
safetyPriorityWeights = attractorWeights 0 4 1 0 0 0

autonomyPriorityWeights : AttractorWeights
autonomyPriorityWeights = attractorWeights 0 1 4 0 0 0

safetyPriorityAppraisesPositive :
  weightedLoss safetyPriorityWeights interventionAutonomyTradeoff
  < weightedGain safetyPriorityWeights interventionAutonomyTradeoff
safetyPriorityAppraisesPositive = four<twelve

autonomyPriorityAppraisesNegative :
  weightedGain autonomyPriorityWeights interventionAutonomyTradeoff
  < weightedLoss autonomyPriorityWeights interventionAutonomyTradeoff
autonomyPriorityAppraisesNegative = three<sixteen

record AttractorWeightDisagreementWitness : Set where
  constructor attractorWeightDisagreementWitness
  field
    firstPositive : weightedLoss safetyPriorityWeights interventionAutonomyTradeoff < weightedGain safetyPriorityWeights interventionAutonomyTradeoff
    secondNegative : weightedGain autonomyPriorityWeights interventionAutonomyTradeoff < weightedLoss autonomyPriorityWeights interventionAutonomyTradeoff

canonicalAttractorWeightDisagreement : AttractorWeightDisagreementWitness
canonicalAttractorWeightDisagreement = attractorWeightDisagreementWitness safetyPriorityAppraisesPositive autonomyPriorityAppraisesNegative

record BranchScore : Set where
  constructor branchScore
  field
    attractorGain informationGain robustnessGain optionalityGain : Nat
    servicingCost switchingCost diversionCost captureCost interactionPenalty : Nat

open BranchScore public

benefitScore : BranchScore → Nat
benefitScore q = attractorGain q + informationGain q + robustnessGain q + optionalityGain q

burdenScore : BranchScore → Nat
burdenScore q = servicingCost q + switchingCost q + diversionCost q + captureCost q + interactionPenalty q

PositiveMarginal : BranchScore → Set
PositiveMarginal q = burdenScore q < benefitScore q

NegativeMarginal : BranchScore → Set
NegativeMarginal q = benefitScore q < burdenScore q

positiveStandaloneBranch : BranchScore
positiveStandaloneBranch = branchScore 1 1 0 1 1 0 0 0 0

negativeAfterInterference : BranchScore
negativeAfterInterference = branchScore 1 1 0 1 1 0 0 0 3

standaloneBranchPositive : PositiveMarginal positiveStandaloneBranch
standaloneBranchPositive = one<three

sameBranchPortfolioNegative : NegativeMarginal negativeAfterInterference
sameBranchPortfolioNegative = three<four

record StandalonePortfolioSignReversalWitness : Set where
  constructor standalonePortfolioSignReversalWitness
  field standalonePositive : PositiveMarginal positiveStandaloneBranch
        portfolioNegative : NegativeMarginal negativeAfterInterference

canonicalStandalonePortfolioSignReversal : StandalonePortfolioSignReversalWitness
canonicalStandalonePortfolioSignReversal = standalonePortfolioSignReversalWitness standaloneBranchPositive sameBranchPortfolioNegative

data Compatibility : Set where
  reinforcesBy : Nat → Compatibility
  independentCompatibility : Compatibility
  softConflictBy : Nat → Compatibility
  hardConflict : Compatibility

AdmissiblePair : Compatibility → Set
AdmissiblePair (reinforcesBy _) = ⊤
AdmissiblePair independentCompatibility = ⊤
AdmissiblePair (softConflictBy _) = ⊤
AdmissiblePair hardConflict = ⊥

hardConflictRejected : AdmissiblePair hardConflict → ⊥
hardConflictRejected ()

record MarginalContextPair : Set where
  constructor marginalContextPair
  field marginalInSmallerContext marginalInLargerContext : Nat

open MarginalContextPair public

DiminishingReturns : MarginalContextPair → Set
DiminishingReturns p = marginalInLargerContext p ≤ marginalInSmallerContext p

ComplementarityThreshold : MarginalContextPair → Set
ComplementarityThreshold p = marginalInSmallerContext p ≤ marginalInLargerContext p

redundantBranchPair : MarginalContextPair
redundantBranchPair = marginalContextPair 4 2

complementaryBranchPair : MarginalContextPair
complementaryBranchPair = marginalContextPair 2 4

redundantBranchDiminishing : DiminishingReturns redundantBranchPair
redundantBranchDiminishing = two≤four

complementaryBranchSupermodular : ComplementarityThreshold complementaryBranchPair
complementaryBranchSupermodular = two≤four

record ExplorationAssessment : Set where
  constructor explorationAssessment
  field expectedInformation opportunityCost explorationServicingCost : Nat

open ExplorationAssessment public

ExplorationJustified : ExplorationAssessment → Set
ExplorationJustified e = opportunityCost e + explorationServicingCost e ≤ expectedInformation e

productiveExploration : ExplorationAssessment
productiveExploration = explorationAssessment 4 1 1

noveltyOnlyExploration : ExplorationAssessment
noveltyOnlyExploration = explorationAssessment 1 1 2

productiveExplorationJustified : ExplorationJustified productiveExploration
productiveExplorationJustified = two≤four

noveltyOnlyExplorationNotJustified : ¬ ExplorationJustified noveltyOnlyExploration
noveltyOnlyExplorationNotJustified = threeNot≤one

record TrajectorySummary : Set where
  constructor trajectorySummary
  field pathVariation netAttractorProgress : Nat

open TrajectorySummary public

canonicalCirculation : TrajectorySummary
canonicalCirculation = trajectorySummary 6 0

record ActivityWithoutProgressWitness : Set where
  constructor activityWithoutProgressWitness
  field activityPositive : 0 < pathVariation canonicalCirculation
        progressZero : netAttractorProgress canonicalCirculation ≡ 0

canonicalActivityWithoutProgress : ActivityWithoutProgressWitness
canonicalActivityWithoutProgress = activityWithoutProgressWitness zero<six refl

record ForecastRealisation : Set where
  constructor mkForecastRealisation
  field expectedDrift realisedDrift : DriftBalance
        evidenceVersionAtForecast evidenceVersionAtObservation : Nat

open ForecastRealisation public

unexpectedSuccess : ForecastRealisation
unexpectedSuccess = mkForecastRealisation (driftBalance 1 3) (driftBalance 3 1) 4 5

unexpectedSuccessExpectedAway : Away (expectedDrift unexpectedSuccess)
unexpectedSuccessExpectedAway = one<three

unexpectedSuccessRealisedToward : Toward (realisedDrift unexpectedSuccess)
unexpectedSuccessRealisedToward = one<three

record SearchCapital : Set where
  constructor mkSearchCapital
  field positiveRouteCapital exclusionCapital reusableInterfaceCapital : Nat

open SearchCapital public

totalSearchCapital : SearchCapital → Nat
totalSearchCapital k = positiveRouteCapital k + exclusionCapital k + reusableInterfaceCapital k

canonicalSearchCapital : SearchCapital
canonicalSearchCapital = mkSearchCapital 3 2 1

canonicalTotalSearchCapitalIsSix : totalSearchCapital canonicalSearchCapital ≡ 6
canonicalTotalSearchCapitalIsSix = refl

record DirectedAttractorPortfolioBoundary : Set where
  constructor directedAttractorPortfolioBoundary
  field
    scalarCapacitySufficientPromotion : Bool
    scalarCapacitySufficientPromotionIsFalse : scalarCapacitySufficientPromotion ≡ false
    positiveStandaloneImpliesPositiveMarginalPromotion : Bool
    positiveStandaloneImpliesPositiveMarginalPromotionIsFalse : positiveStandaloneImpliesPositiveMarginalPromotion ≡ false
    shortReliefImpliesLongProgressPromotion : Bool
    shortReliefImpliesLongProgressPromotionIsFalse : shortReliefImpliesLongProgressPromotion ≡ false
    sameForecastImpliesSameAppraisalPromotion : Bool
    sameForecastImpliesSameAppraisalPromotionIsFalse : sameForecastImpliesSameAppraisalPromotion ≡ false
    aggregateServiceableImpliesEachBranchViablePromotion : Bool
    aggregateServiceableImpliesEachBranchViablePromotionIsFalse : aggregateServiceableImpliesEachBranchViablePromotion ≡ false
    activityImpliesProgressPromotion : Bool
    activityImpliesProgressPromotionIsFalse : activityImpliesProgressPromotion ≡ false
    goodOutcomeImpliesHighExAnteProbabilityPromotion : Bool
    goodOutcomeImpliesHighExAnteProbabilityPromotionIsFalse : goodOutcomeImpliesHighExAnteProbabilityPromotion ≡ false
    noveltyImpliesUsefulExplorationPromotion : Bool
    noveltyImpliesUsefulExplorationPromotionIsFalse : noveltyImpliesUsefulExplorationPromotion ≡ false
    finiteToyEqualsCalibratedControlModelPromotion : Bool
    finiteToyEqualsCalibratedControlModelPromotionIsFalse : finiteToyEqualsCalibratedControlModelPromotion ≡ false
    boundaryReading : String

open DirectedAttractorPortfolioBoundary public

canonicalDirectedAttractorPortfolioBoundary : DirectedAttractorPortfolioBoundary
canonicalDirectedAttractorPortfolioBoundary =
  directedAttractorPortfolioBoundary
    false refl false refl false refl false refl false refl false refl false refl false refl false refl
    "A branch portfolio is evaluated by resource-wise feasibility, multi-horizon drift, information, robustness, optionality, interaction, switching, diversion, capture, and attractor weights. Raw count, aggregate affordability, activity, novelty, or a lucky realised outcome cannot silently stand in for positive portfolio value."

sourceAtlasCount : Nat
sourceAtlasCount = Sources.canonicalDirectedPortfolioSourceCount
