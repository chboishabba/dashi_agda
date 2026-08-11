module DASHI.Biology.DirectedBranchPolicyControl where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.DirectedAttractorPortfolioCalculus as Directed
import DASHI.Biology.Levin.CompetentGoalExecution as Levin

data PortfolioState : Set where
  initialState nearDesiredState desiredState trapState circulationState : PortfolioState

data PortfolioGoal : Set where reachDesiredGoal : PortfolioGoal

data PortfolioCommand : Set where moveTowardDesiredCommand : PortfolioCommand

data BranchPolicy : Set where
  alignedPolicy robustDetourPolicy exploratoryPolicy diffusedPolicy : BranchPolicy
  trapDirectedPolicy circulationPolicy : BranchPolicy

interpretCommand : PortfolioCommand → PortfolioGoal
interpretCommand moveTowardDesiredCommand = reachDesiredGoal

acceptCommand : PortfolioState → PortfolioCommand → Bool
acceptCommand _ _ = true

executePolicy : BranchPolicy → PortfolioState → PortfolioState
executePolicy alignedPolicy initialState = desiredState
executePolicy robustDetourPolicy initialState = desiredState
executePolicy exploratoryPolicy initialState = nearDesiredState
executePolicy diffusedPolicy initialState = initialState
executePolicy trapDirectedPolicy initialState = trapState
executePolicy circulationPolicy initialState = circulationState
executePolicy _ state = state

satisfiesGoal : PortfolioState → PortfolioGoal → Bool
satisfiesGoal desiredState reachDesiredGoal = true
satisfiesGoal _ reachDesiredGoal = false

samePolicy : BranchPolicy → BranchPolicy → Bool
samePolicy alignedPolicy alignedPolicy = true
samePolicy robustDetourPolicy robustDetourPolicy = true
samePolicy exploratoryPolicy exploratoryPolicy = true
samePolicy diffusedPolicy diffusedPolicy = true
samePolicy trapDirectedPolicy trapDirectedPolicy = true
samePolicy circulationPolicy circulationPolicy = true
samePolicy _ _ = false

discoverPolicy : PortfolioState → PortfolioGoal → BranchPolicy
discoverPolicy _ reachDesiredGoal = alignedPolicy

finitePortfolioGoalSystem : Levin.GoalExecutionSystem
finitePortfolioGoalSystem = record
  { State = PortfolioState
  ; Goal = PortfolioGoal
  ; Command = PortfolioCommand
  ; Policy = BranchPolicy
  ; interpret = interpretCommand
  ; accept = acceptCommand
  ; discover = discoverPolicy
  ; execute = executePolicy
  ; satisfies = satisfiesGoal
  ; samePolicy = samePolicy
  }

canonicalCompetentPortfolioExecution : Levin.CompetentExecutionWitness finitePortfolioGoalSystem
canonicalCompetentPortfolioExecution = record
  { initial = initialState
  ; command = moveTowardDesiredCommand
  ; commandAccepted = refl
  ; reachesCommandedGoal = refl
  }

canonicalGoalUnderdeterminesPolicy : Levin.GoalUnderdeterminesTrajectoryWitness finitePortfolioGoalSystem
canonicalGoalUnderdeterminesPolicy = record
  { initial = initialState
  ; command = moveTowardDesiredCommand
  ; policy₁ = alignedPolicy
  ; policy₂ = robustDetourPolicy
  ; distinctPolicies = refl
  ; policy₁Succeeds = refl
  ; policy₂Succeeds = refl
  }

potential : PortfolioState → Nat
potential initialState = 3
potential nearDesiredState = 1
potential desiredState = 0
potential trapState = 5
potential circulationState = 3

towardTransport : BranchPolicy → PortfolioState → Nat
towardTransport policy state = potential state ∸ potential (executePolicy policy state)

awayTransport : BranchPolicy → PortfolioState → Nat
awayTransport policy state = potential (executePolicy policy state) ∸ potential state

alignedTransportIsThree : towardTransport alignedPolicy initialState ≡ 3
alignedTransportIsThree = refl

explorationTransportIsTwo : towardTransport exploratoryPolicy initialState ≡ 2
explorationTransportIsTwo = refl

trapTransportAwayIsTwo : awayTransport trapDirectedPolicy initialState ≡ 2
trapTransportAwayIsTwo = refl

circulationHasZeroNetTransport :
  towardTransport circulationPolicy initialState ≡ 0
  × awayTransport circulationPolicy initialState ≡ 0
circulationHasZeroNetTransport = refl , refl

policyValueAtInitial : BranchPolicy → Nat
policyValueAtInitial alignedPolicy = 4
policyValueAtInitial robustDetourPolicy = 3
policyValueAtInitial exploratoryPolicy = 2
policyValueAtInitial diffusedPolicy = 1
policyValueAtInitial trapDirectedPolicy = 0
policyValueAtInitial circulationPolicy = 0

four≤four : 4 ≤ 4
four≤four = s≤s (s≤s (s≤s (s≤s z≤n)))

one≤four : 1 ≤ 4
one≤four = s≤s z≤n

alignedDominates : (policy : BranchPolicy) → policyValueAtInitial policy ≤ policyValueAtInitial alignedPolicy
alignedDominates alignedPolicy = four≤four
alignedDominates robustDetourPolicy = Directed.three≤four
alignedDominates exploratoryPolicy = Directed.two≤four
alignedDominates diffusedPolicy = one≤four
alignedDominates trapDirectedPolicy = z≤n
alignedDominates circulationPolicy = z≤n

record OptimalAtInitial (policy : BranchPolicy) : Set where
  constructor optimalAtInitial
  field dominatesEveryPolicy : (candidate : BranchPolicy) → policyValueAtInitial candidate ≤ policyValueAtInitial policy

alignedPolicyOptimal : OptimalAtInitial alignedPolicy
alignedPolicyOptimal = optimalAtInitial alignedDominates

data ReachableBasin : Set where desiredBasin nearDesiredBasin statusQuoBasin adverseBasin loopBasin : ReachableBasin

policyBasin : BranchPolicy → ReachableBasin
policyBasin alignedPolicy = desiredBasin
policyBasin robustDetourPolicy = desiredBasin
policyBasin exploratoryPolicy = nearDesiredBasin
policyBasin diffusedPolicy = statusQuoBasin
policyBasin trapDirectedPolicy = adverseBasin
policyBasin circulationPolicy = loopBasin

nominallyDistinctSameBasin : policyBasin alignedPolicy ≡ policyBasin robustDetourPolicy
nominallyDistinctSameBasin = refl

policiesDistinct : samePolicy alignedPolicy robustDetourPolicy ≡ false
policiesDistinct = refl

record RawTwoEffectiveOneWitness : Set where
  constructor rawTwoEffectiveOneWitness
  field
    distinctSurfacePolicies : samePolicy alignedPolicy robustDetourPolicy ≡ false
    sameReachableBasin : policyBasin alignedPolicy ≡ policyBasin robustDetourPolicy
    rawCount : Nat
    rawCountIsTwo : rawCount ≡ 2
    effectiveCount : Nat
    effectiveCountIsOne : effectiveCount ≡ 1

canonicalRawTwoEffectiveOne : RawTwoEffectiveOneWitness
canonicalRawTwoEffectiveOne = rawTwoEffectiveOneWitness refl refl 2 refl 1 refl

record PolicyFlow : Set where
  constructor policyFlow
  field alignedFlow robustFlow exploratoryFlow diffusedFlow trapFlow circulationFlow : Nat

open PolicyFlow public

flowToward : PolicyFlow → Nat
flowToward f = 2 * alignedFlow f + 2 * robustFlow f + exploratoryFlow f

flowAway : PolicyFlow → Nat
flowAway f = diffusedFlow f + 2 * trapFlow f

NetToward : PolicyFlow → Set
NetToward f = flowAway f < flowToward f

FlowNeutral : PolicyFlow → Set
FlowNeutral f = flowToward f ≡ flowAway f

concentratedFlow : PolicyFlow
concentratedFlow = policyFlow 2 0 0 0 0 0

diffusedAdverseFlow : PolicyFlow
diffusedAdverseFlow = policyFlow 1 0 0 0 1 0

zero<four : 0 < 4
zero<four = s≤s z≤n

concentratedFlowNetToward : NetToward concentratedFlow
concentratedFlowNetToward = zero<four

diffusedAdverseFlowNeutral : FlowNeutral diffusedAdverseFlow
diffusedAdverseFlowNeutral = refl

record DirectedBranchPolicyBoundary : Set where
  constructor directedBranchPolicyBoundary
  field
    commandDeterminesMicrotrajectoryPromotion : Bool
    commandDeterminesMicrotrajectoryPromotionIsFalse : commandDeterminesMicrotrajectoryPromotion ≡ false
    goalHasUniqueSuccessfulPolicyPromotion : Bool
    goalHasUniqueSuccessfulPolicyPromotionIsFalse : goalHasUniqueSuccessfulPolicyPromotion ≡ false
    nominalPolicyCountEqualsEffectiveBasinCountPromotion : Bool
    nominalPolicyCountEqualsEffectiveBasinCountPromotionIsFalse : nominalPolicyCountEqualsEffectiveBasinCountPromotion ≡ false
    activeFlowImpliesNetAttractorProgressPromotion : Bool
    activeFlowImpliesNetAttractorProgressPromotionIsFalse : activeFlowImpliesNetAttractorProgressPromotion ≡ false
    finiteOptimalityEqualsRealWorldCalibrationPromotion : Bool
    finiteOptimalityEqualsRealWorldCalibrationPromotionIsFalse : finiteOptimalityEqualsRealWorldCalibrationPromotion ≡ false
    boundaryReading : String

open DirectedBranchPolicyBoundary public

canonicalDirectedBranchPolicyBoundary : DirectedBranchPolicyBoundary
canonicalDirectedBranchPolicyBoundary =
  directedBranchPolicyBoundary false refl false refl false refl false refl false refl
    "A finite transition system computes attractor transport and certifies an optimal policy while preserving goal underdetermination, effective-basin quotienting, flow interference, and non-calibration boundaries."
