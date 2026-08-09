module DASHI.Foundations.Base369ProcessBranchAttractorExact where

------------------------------------------------------------------------
-- A live branch is not merely a possible endpoint.  It may carry accumulated
-- state, search capital, expiry, servicing cost, information value, and a
-- direction relative to layered attractors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

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
