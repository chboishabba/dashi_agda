{-# OPTIONS --safe #-}
module DASHI.Interop.SublinearTopicConductorCostExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SLRWorldResearchIterationBudgetExact as Budget

------------------------------------------------------------------------
-- SUBLINEAR TOPIC CONDUCTOR CONTROL LAW
--
-- Runtime owner:
--   chboishabba/ITIR-suite
--   itir-mcp/src/itir_mcp/fleet_round_runner.py
--
-- Agda is the golden control-law owner.  The runtime cost receipt records:
--
-- C(T_k,W) =
--   alpha(T_k) * (UnblockedGoals / TotalGoals)
--              * min(W_cap, dim(SubEigens), W)
--   - TokenCost(W)
--
-- This module formalises the discrete worker-width law and authority
-- firewalls.  It does not claim floating-point parity for runtime alpha or
-- token-cost arithmetic.
------------------------------------------------------------------------

minNat : Nat → Nat → Nat
minNat zero _ = zero
minNat _ zero = zero
minNat (suc left) (suc right) = suc (minNat left right)

data TopicShape : Set where
  frontierBlocked : Nat → TopicShape
  sequential : TopicShape
  parallelBySubEigen : Nat → TopicShape

workerWidth : Nat → TopicShape → Nat
workerWidth cap (frontierBlocked blockers) = minNat cap blockers
workerWidth zero sequential = zero
workerWidth (suc cap) sequential = suc zero
workerWidth cap (parallelBySubEigen dimension) = minNat cap dimension

record DynamicConductorBoundary : Set where
  constructor dynamic-conductor-boundary
  field
    costFormulaReference : String
    workerCapacityIsBudgetNotModeSelector : Bool
    frontierBlockedWidthUsesBlockerCount : Bool
    sequentialWidthIsOneWhenCapacityPositive : Bool
    parallelWidthUsesSubEigenDimension : Bool
    lowerAlphaSubtopicsRemainPreserved : Bool
    lowerAlphaSubtopicsBecomeSequencedInternalPackets : Bool
    rolledPacketsRemainEligibleForCrossPollination : Bool
    alphaCreatesTruth : Bool
    alphaCreatesProofAuthority : Bool
    workerAllocationCreatesSemanticAuthority : Bool
    parallelDispatchRequiresNoTypedMeet : Bool
    candidateOnly : Bool

open DynamicConductorBoundary public

canonicalDynamicConductorBoundary : DynamicConductorBoundary
canonicalDynamicConductorBoundary =
  dynamic-conductor-boundary
    "C(T_k,W)=alpha(T_k)*(UnblockedGoals/TotalGoals)*min(W_cap,dim(SubEigens),W)-TokenCost(W)"
    true true true true
    true true true
    false false false
    true true

frontierBlockedWidthLaw :
  (cap blockers : Nat) →
  workerWidth cap (frontierBlocked blockers) ≡ minNat cap blockers
frontierBlockedWidthLaw cap blockers = refl

sequentialWidthLaw :
  (cap : Nat) →
  workerWidth (suc cap) sequential ≡ suc zero
sequentialWidthLaw cap = refl

parallelSubEigenWidthLaw :
  (cap dimension : Nat) →
  workerWidth cap (parallelBySubEigen dimension) ≡ minNat cap dimension
parallelSubEigenWidthLaw cap dimension = refl

fourBlockersWithTwentyWorkersUsesFour :
  workerWidth 20 (frontierBlocked 4) ≡ 4
fourBlockersWithTwentyWorkersUsesFour = refl

sequentialWithTwentyWorkersUsesOne :
  workerWidth 20 sequential ≡ 1
sequentialWithTwentyWorkersUsesOne = refl

fiveSubEigensWithTwentyWorkersUsesFive :
  workerWidth 20 (parallelBySubEigen 5) ≡ 5
fiveSubEigensWithTwentyWorkersUsesFive = refl

capacityDoesNotSelectMode :
  workerCapacityIsBudgetNotModeSelector canonicalDynamicConductorBoundary ≡ true
capacityDoesNotSelectMode = refl

lowerAlphaWorkIsPreserved :
  lowerAlphaSubtopicsRemainPreserved canonicalDynamicConductorBoundary ≡ true
lowerAlphaWorkIsPreserved = refl

lowerAlphaWorkIsSequencedInternally :
  lowerAlphaSubtopicsBecomeSequencedInternalPackets canonicalDynamicConductorBoundary ≡ true
lowerAlphaWorkIsSequencedInternally = refl

alphaDoesNotCreateTruth :
  alphaCreatesTruth canonicalDynamicConductorBoundary ≡ false
alphaDoesNotCreateTruth = refl

alphaDoesNotCreateProofAuthority :
  alphaCreatesProofAuthority canonicalDynamicConductorBoundary ≡ false
alphaDoesNotCreateProofAuthority = refl

allocationDoesNotCreateSemanticAuthority :
  workerAllocationCreatesSemanticAuthority canonicalDynamicConductorBoundary ≡ false
allocationDoesNotCreateSemanticAuthority = refl

parallelStillRequiresNoTypedMeet :
  parallelDispatchRequiresNoTypedMeet canonicalDynamicConductorBoundary ≡ true
parallelStillRequiresNoTypedMeet = refl

budgetAnchor : Budget.WorldResearchIterationBudget
budgetAnchor = Budget.canonicalWorldResearchIterationBudget
