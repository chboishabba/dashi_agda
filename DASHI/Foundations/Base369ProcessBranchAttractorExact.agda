module DASHI.Foundations.Base369ProcessBranchAttractorExact where

------------------------------------------------------------------------
-- A live branch is not merely a possible endpoint.  It may carry accumulated
-- state, search capital, expiry, servicing cost, information value, and a
-- direction relative to layered attractors.
--
-- This module also makes two stronger distinctions executable:
--
-- * serviceability is not attractor alignment;
-- * nominal branch multiplicity is not effective dynamical diversity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )

open import DASHI.Foundations.Base369LayeredAttractorAndCoarseFineExact using
  ( LayeredAttractor
  ; HorizonDrift
  ; horizonDrift
  ; Depth9
  ; Depth6
  ; Horizon3
  ; project9To6
  ; project9To3
  )

record ProcessBranch
  (Goal State Provenance : Set) : Set₁ where
  constructor processBranch
  field
    goal : Goal
    accumulatedState : State
    provenance : Provenance
    live : Bool
    servicingCost : Nat
    informationValue : Nat
    diversionCost : Nat
    immediateDirection : TriTruth
    mediumDirection : TriTruth
    longDirection : TriTruth

open ProcessBranch public

branchDrift :
  {Goal State Provenance : Set} →
  ProcessBranch Goal State Provenance → HorizonDrift
branchDrift branch =
  horizonDrift
    (immediateDirection branch)
    (mediumDirection branch)
    (longDirection branch)

------------------------------------------------------------------------
-- Outcome-zero and process-zero are separated.
------------------------------------------------------------------------

data GoalStatus : Set where
  outcomeReached
  outcomeUnstarted
  outcomeSearching
  outcomePending
  outcomeBlocked
  outcomeExpired
  outcomeHandover
  outcomeAbandoned : GoalStatus

record GoalProcessState (SearchState : Set) : Set where
  constructor goalProcessState
  field
    status : GoalStatus
    searchState : SearchState

------------------------------------------------------------------------
-- Branch-value orientation is a signed reduction of a richer fibre.
------------------------------------------------------------------------

data BranchValueReason : Set where
  attractorAligned
  exploratoryInformation
  redundantCirculation
  adverseDrift
  trapAttractor
  capacityDestructive
  interferenceLoss : BranchValueReason

record FibredBranchValue : Set where
  constructor fibredBranchValue
  field
    branchOrientation : TriTruth
    reason : BranchValueReason

open FibredBranchValue public

alignedValue : FibredBranchValue
alignedValue = fibredBranchValue tri-high attractorAligned

exploratoryValue : FibredBranchValue
exploratoryValue = fibredBranchValue tri-mid exploratoryInformation

circulatingValue : FibredBranchValue
circulatingValue = fibredBranchValue tri-mid redundantCirculation

adverseValue : FibredBranchValue
adverseValue = fibredBranchValue tri-low adverseDrift

------------------------------------------------------------------------
-- Symmetry-aware optionality.
------------------------------------------------------------------------

record BranchSimilarity (Branch : Set) : Set₁ where
  constructor branchSimilarity
  field
    corresponds : Branch → Branch → Set
    sameImmediate : Branch → Branch → Bool
    sameMedium : Branch → Branch → Bool
    sameLong : Branch → Branch → Bool

record EffectiveBranchOrbit (Branch : Set) : Set₁ where
  constructor effectiveBranchOrbit
  field
    representative : Branch
    member : Branch → Set
    operationalCopies : Nat

------------------------------------------------------------------------
-- A concrete quotient example: two nominal branches can be one dynamical
-- orbit while still requiring two operational copies to be serviced.
------------------------------------------------------------------------

data DuplicateBranch : Set where
  duplicateLeft
  duplicateRight : DuplicateBranch

data DuplicateOrbit : Set where
  sharedDuplicateOrbit : DuplicateOrbit

duplicateOrbitOf : DuplicateBranch → DuplicateOrbit
duplicateOrbitOf duplicateLeft = sharedDuplicateOrbit
duplicateOrbitOf duplicateRight = sharedDuplicateOrbit

nominalDuplicateCount : Nat
nominalDuplicateCount = 2

effectiveDuplicateOrbitCount : Nat
effectiveDuplicateOrbitCount = 1

operationalDuplicateCopies : Nat
operationalDuplicateCopies = 2

nominalDuplicateCountIs2 : nominalDuplicateCount ≡ 2
nominalDuplicateCountIs2 = refl

effectiveDuplicateOrbitCountIs1 : effectiveDuplicateOrbitCount ≡ 1
effectiveDuplicateOrbitCountIs1 = refl

bothNominalCopiesShareOrbit :
  duplicateOrbitOf duplicateLeft ≡ duplicateOrbitOf duplicateRight
bothNominalCopiesShareOrbit = refl

------------------------------------------------------------------------
-- 369-aware symmetry is layered.  Equality at the full 9-coordinate depth
-- implies equality of its 6- and 3-coordinate projections, but the converse
-- is deliberately not provided.
------------------------------------------------------------------------

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record SameAt3 (x y : Depth9) : Set where
  constructor sameAt3
  field same3 : project9To3 x ≡ project9To3 y

record SameAt6 (x y : Depth9) : Set where
  constructor sameAt6
  field same6 : project9To6 x ≡ project9To6 y

record SameAt9 (x y : Depth9) : Set where
  constructor sameAt9
  field same9 : x ≡ y

sameAt9ImpliesSameAt6 : {x y : Depth9} → SameAt9 x y → SameAt6 x y
sameAt9ImpliesSameAt6 witness =
  sameAt6 (cong project9To6 (SameAt9.same9 witness))

sameAt9ImpliesSameAt3 : {x y : Depth9} → SameAt9 x y → SameAt3 x y
sameAt9ImpliesSameAt3 witness =
  sameAt3 (cong project9To3 (SameAt9.same9 witness))

------------------------------------------------------------------------
-- Marginal branch value with an exact positive-margin certificate.
--
-- gain = attractor drift + novel information + independent robustness
--        + constructive interaction
-- loss = servicing + diversion + destructive interference + redundancy
--
-- A PositiveMarginal witness is stronger than a Boolean `beneficial`: it
-- supplies the exact natural-number slack by which gain exceeds loss.
------------------------------------------------------------------------

record MarginalBranchBudget : Set where
  constructor marginalBranchBudget
  field
    attractorGain : Nat
    novelInformationGain : Nat
    independentRobustnessGain : Nat
    constructiveInteractionGain : Nat
    serviceCost : Nat
    diversionCost : Nat
    interferenceCost : Nat
    redundancyCost : Nat

open MarginalBranchBudget public

totalGain : MarginalBranchBudget → Nat
totalGain budget =
  attractorGain budget
  + novelInformationGain budget
  + independentRobustnessGain budget
  + constructiveInteractionGain budget

totalLoss : MarginalBranchBudget → Nat
totalLoss budget =
  serviceCost budget
  + diversionCost budget
  + interferenceCost budget
  + redundancyCost budget

record PositiveMarginal (budget : MarginalBranchBudget) : Set where
  constructor positiveMarginal
  field
    margin : Nat
    gainExceedsLossExactly :
      totalGain budget ≡ suc margin + totalLoss budget

open PositiveMarginal public

beneficialBudgetExample : MarginalBranchBudget
beneficialBudgetExample =
  marginalBranchBudget
    3  -- attractor gain
    2  -- novel information
    1  -- independent robustness
    1  -- constructive interaction
    1  -- servicing
    1  -- diversion
    1  -- destructive interference
    0  -- redundancy

beneficialBudgetExampleHasPositiveMargin :
  PositiveMarginal beneficialBudgetExample
beneficialBudgetExampleHasPositiveMargin =
  positiveMarginal 3 refl

------------------------------------------------------------------------
-- Capacity and direction are independent.  The following pair fits inside its
-- capacity exactly while its opposed directions reduce to a neutral local
-- resultant.  Thus `serviceable` does not imply `attractor-aligned`.
------------------------------------------------------------------------

record ServiceableCost : Set where
  constructor serviceableCost
  field
    usedCapacity : Nat
    totalCapacity : Nat
    spareCapacity : Nat
    fitsExactly : usedCapacity + spareCapacity ≡ totalCapacity

open ServiceableCost public

data DirectionPairReduction : TriTruth → TriTruth → TriTruth → Set where
  alignedAligned : DirectionPairReduction tri-high tri-high tri-high
  adverseAdverse : DirectionPairReduction tri-low tri-low tri-low
  positiveNegativeCancel : DirectionPairReduction tri-high tri-low tri-mid
  negativePositiveCancel : DirectionPairReduction tri-low tri-high tri-mid
  neutralNeutral : DirectionPairReduction tri-mid tri-mid tri-mid

record ServiceableDirectionalDiffusion : Set where
  constructor serviceableDirectionalDiffusion
  field
    capacityWitness : ServiceableCost
    firstDirection : TriTruth
    secondDirection : TriTruth
    netDirection : TriTruth
    directionalReduction :
      DirectionPairReduction firstDirection secondDirection netDirection

open ServiceableDirectionalDiffusion public

serviceableButDirectionallyCancelled : ServiceableDirectionalDiffusion
serviceableButDirectionallyCancelled =
  serviceableDirectionalDiffusion
    (serviceableCost 2 3 1 refl)
    tri-high
    tri-low
    tri-mid
    positiveNegativeCancel

serviceableDiffusionIsNeutral :
  netDirection serviceableButDirectionallyCancelled ≡ tri-mid
serviceableDiffusionIsNeutral = refl

------------------------------------------------------------------------
-- Adding a branch is beneficial only with a proof-bearing marginal witness.
------------------------------------------------------------------------

record BeneficialBranchAddition (Branch : Set) : Set₁ where
  constructor beneficialBranchAddition
  field
    existing : Branch → Set
    candidate : Branch
    serviceable : Bool
    attractorRelevant : Bool
    informationUseful : Bool
    interferenceControlled : Bool
    serviceableIsTrue : serviceable ≡ true
    attractorRelevantIsTrue : attractorRelevant ≡ true
    interferenceControlledIsTrue : interferenceControlled ≡ true

-- No constructor turns mere liveness or serviceability into benefit.
