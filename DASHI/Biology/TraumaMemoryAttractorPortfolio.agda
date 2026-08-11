module DASHI.Biology.TraumaMemoryAttractorPortfolio where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.GuardedPropositionResponseTree as Guarded
import DASHI.Biology.PredictiveMetastabilityTraumaBridge as Predictive
import DASHI.Biology.ChildAuthorityTraumaSourceAtlas as Sources

data FeasibilityLayer : Set where
  logicalLayer institutionalLayer economicLayer agentLayer capacityLayer temporalLayer : FeasibilityLayer

record LivenessVector : Set where
  constructor livenessVector
  field
    logicalLive institutionalLive economicLive agentLive capacityLive temporalLive : Bool

open LivenessVector public

record BranchCostVector : Set where
  constructor branchCostVector
  field
    attentionCost moneyCost timeCost emotionalCost administrativeCost legalCost socialCost : Nat

open BranchCostVector public

data AttractorKind : Set where desiredAttractor safetyAttractor lifeGoalAttractor adverseAttractor trapAttractor : AttractorKind

data DriftDirection : Set where towardAttractor tangentCirculation awayFromAttractor : DriftDirection

data InteractionKind : Set where reinforcingInteraction independentInteraction interferingInteraction hardConflictInteraction : InteractionKind

data FeasibilityClass : Set where infeasibleClass serviceableClass fragileClass overloadingClass : FeasibilityClass

data DirectionClass : Set where
  attractorAlignedClass informationalClass orthogonalClass circulatoryClass adverseClass trapDirectedClass : DirectionClass

record BranchValue : Set where
  constructor branchValue
  field
    expectedDrift : DriftDirection
    informationGain robustnessValue optionalityValue diversionCost switchingCost lockInRisk : Nat
    feasibilityClass : FeasibilityClass
    directionClass : DirectionClass

open BranchValue public

record BranchInteraction : Set where
  constructor branchInteraction
  field
    leftDecisionToken rightDecisionToken : Nat
    interactionKind : InteractionKind
    interactionReading : String

open BranchInteraction public

data ClosureReason : Set where
  closedBySelection closedByRejection closedByExpiry closedByInfeasibility : ClosureReason
  closedByCapacityOverload closedByExternalBlock closedByRevocation : ClosureReason
  closedBySupersession stillOpen : ClosureReason

record BranchMemory : Set where
  constructor branchMemory
  field
    memoryNode : Guarded.PropositionNode
    statusHistory : List Guarded.BranchStatus
    zeroHistory : List Guarded.ZeroKind
    liveness : LivenessVector
    cost : BranchCostVector
    value : BranchValue
    expectedDirectionAtOpening realisedDirection : DriftDirection
    accumulatedDepth reusableSearchCapital : Nat
    blockingDependencies : List String
    competingDecisionTokens : List Nat
    terminalReason : ClosureReason
    provenance : String

open BranchMemory public

data LearningResidueKind : Set where
  eligibilityResidue documentaryRequirementResidue deadlineResidue contactResidue : LearningResidueKind
  blockedBasinResidue interactionResidue noReusableResidue : LearningResidueKind

record BranchLearningResidue : Set where
  constructor branchLearningResidue
  field
    sourceDecisionToken : Nat
    residueKinds : List LearningResidueKind
    futureReusable : Bool
    informationValue : Nat
    residueReading : String

record BranchPortfolio : Set where
  constructor branchPortfolio
  field
    rawBranchCount effectiveBasinCount : Nat
    serviceable attractorRelevant jointlyCoherent desiredAttractorProgress : Bool
    portfolioReading : String

open BranchPortfolio public

smallAlignedPortfolio : BranchPortfolio
smallAlignedPortfolio = branchPortfolio 1 1 true true true true
  "One serviceable branch aligned with the desired attractor."

largerDiffusedPortfolio : BranchPortfolio
largerDiffusedPortfolio = branchPortfolio 2 1 true false false false
  "Two serviceable nominal branches share one ineffective basin and diffuse flow away from the desired attractor."

smallAlignedPortfolioCountIsOne : rawBranchCount smallAlignedPortfolio ≡ 1
smallAlignedPortfolioCountIsOne = refl

largerDiffusedPortfolioCountIsTwo : rawBranchCount largerDiffusedPortfolio ≡ 2
largerDiffusedPortfolioCountIsTwo = refl

largerRawCountDoesNotForceProgress : desiredAttractorProgress largerDiffusedPortfolio ≡ false
largerRawCountDoesNotForceProgress = refl

largerRawCountDoesNotForceEffectiveDiversity : effectiveBasinCount largerDiffusedPortfolio ≡ 1
largerRawCountDoesNotForceEffectiveDiversity = refl

record MoreBranchesWithoutMoreProgressWitness : Set where
  constructor moreBranchesWithoutMoreProgressWitness
  field
    smallerPortfolio largerPortfolio : BranchPortfolio
    smallerCount : rawBranchCount smallerPortfolio ≡ 1
    largerCount : rawBranchCount largerPortfolio ≡ 2
    smallerProgress : desiredAttractorProgress smallerPortfolio ≡ true
    largerNoProgress : desiredAttractorProgress largerPortfolio ≡ false
    largerNoExtraBasin : effectiveBasinCount largerPortfolio ≡ 1

canonicalMoreBranchesWithoutMoreProgressWitness : MoreBranchesWithoutMoreProgressWitness
canonicalMoreBranchesWithoutMoreProgressWitness =
  moreBranchesWithoutMoreProgressWitness smallAlignedPortfolio largerDiffusedPortfolio refl refl refl refl refl

data MarginalValueSign : Set where negativeMarginalValue zeroMarginalValue positiveMarginalValue : MarginalValueSign

record MarginalBranchAssessment : Set where
  constructor marginalBranchAssessment
  field
    candidateDecisionToken : Nat
    driftContribution : DriftDirection
    informationContribution robustnessContribution optionalityContribution : Nat
    interactionTerms : List BranchInteraction
    servicingBurden : BranchCostVector
    captureRisk : Nat
    marginalSign : MarginalValueSign
    assessmentReading : String

data TraumaPolicyDeformation : Set where
  branchHoardingDeformation prematureClosureDeformation threatAttractorSubstitution : TraumaPolicyDeformation
  contextSensitiveConstraintLearning : TraumaPolicyDeformation

data MemoryCompressionKind : Set where
  topologyPreservingCompression terminalOutcomeOnlyCompression : MemoryCompressionKind
  allNonSuccessCollapsedToZero expectedRealisedDriftCollapsed : MemoryCompressionKind

predictiveTraumaBridge : Predictive.PredictiveMetastabilityTraumaBridge
predictiveTraumaBridge = Predictive.canonicalPredictiveMetastabilityTraumaBridge

sourceAtlasCount : Nat
sourceAtlasCount = Sources.canonicalChildAuthorityTraumaSourceCount

record TraumaMemoryAttractorPromotionBoundary : Set where
  constructor traumaMemoryAttractorPromotionBoundary
  field
    moreBranchesAlwaysBetterPromotion : Bool
    moreBranchesAlwaysBetterPromotionIsFalse : moreBranchesAlwaysBetterPromotion ≡ false
    serviceabilityImpliesUsefulnessPromotion : Bool
    serviceabilityImpliesUsefulnessPromotionIsFalse : serviceabilityImpliesUsefulnessPromotion ≡ false
    logicalLivenessEqualsAgentLivenessPromotion : Bool
    logicalLivenessEqualsAgentLivenessPromotionIsFalse : logicalLivenessEqualsAgentLivenessPromotion ≡ false
    rawActivityEqualsProgressPromotion : Bool
    rawActivityEqualsProgressPromotionIsFalse : rawActivityEqualsProgressPromotion ≡ false
    localReliefEqualsLongTermProgressPromotion : Bool
    localReliefEqualsLongTermProgressPromotionIsFalse : localReliefEqualsLongTermProgressPromotion ≡ false
    operationalClosureEqualsErasurePromotion : Bool
    operationalClosureEqualsErasurePromotionIsFalse : operationalClosureEqualsErasurePromotion ≡ false
    expiredMeansRejectedPromotion : Bool
    expiredMeansRejectedPromotionIsFalse : expiredMeansRejectedPromotion ≡ false
    failedBranchMeansNoLearningPromotion : Bool
    failedBranchMeansNoLearningPromotionIsFalse : failedBranchMeansNoLearningPromotion ≡ false
    traumaAlwaysHoardingPromotion : Bool
    traumaAlwaysHoardingPromotionIsFalse : traumaAlwaysHoardingPromotion ≡ false
    traumaAlwaysPruningPromotion : Bool
    traumaAlwaysPruningPromotionIsFalse : traumaAlwaysPruningPromotion ≡ false
    calibratedClinicalModelPromotion : Bool
    calibratedClinicalModelPromotionIsFalse : calibratedClinicalModelPromotion ≡ false
    boundaryReading : String

open TraumaMemoryAttractorPromotionBoundary public

canonicalTraumaMemoryAttractorPromotionBoundary : TraumaMemoryAttractorPromotionBoundary
canonicalTraumaMemoryAttractorPromotionBoundary =
  traumaMemoryAttractorPromotionBoundary
    false refl false refl false refl false refl false refl false refl false refl false refl false refl false refl false refl
    "Optionality is the value of reachable, serviceable, non-destructive structure around desired future basins, not raw branch count. Memory preserves live, blocked, expired, traversed, and learned branch topology. Trauma may bias policy toward hoarding, premature closure, or threat-attractor substitution, but no clinical diagnosis is promoted."

canonicalMoreBranchesAlwaysBetterPromotionFalse :
  moreBranchesAlwaysBetterPromotion canonicalTraumaMemoryAttractorPromotionBoundary ≡ false
canonicalMoreBranchesAlwaysBetterPromotionFalse =
  moreBranchesAlwaysBetterPromotionIsFalse canonicalTraumaMemoryAttractorPromotionBoundary
