{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.SentenceCloseKernelDecompositionExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- E0c: performance observation is not semantic authority.
--
-- Once producer admission is fixed-per-family, remaining sentence-close wall
-- may come from secondary trigger/reconciliation kernels.  Profiling is allowed
-- to decompose that physical wall, but the measured ranking cannot change the
-- semantic authority or license disabling a kernel.
------------------------------------------------------------------------

record SentenceCloseKernelWork : Set where
  constructor sentenceCloseKernelWork
  field
    producerAdmissionWork : Nat
    mentionDerivationWork : Nat
    adjacencyMaterializationWork : Nat
    demandPlanningWork : Nat
    ancestorPublicationWork : Nat
    otherDerivedWork : Nat

open SentenceCloseKernelWork public

record SentenceCloseKernelProfileReceipt : Set where
  constructor sentenceCloseKernelProfileReceipt
  field
    trackedFunctionCount : Nat
    sourceTokenRescanCount : Nat
    semanticAuthorityChangedByProfiler : Bool
    triggersDisabled : Bool
    functionsReplaced : Bool
    zeroSourceTokenRescan : sourceTokenRescanCount ≡ zero
    profilerDoesNotChangeAuthority : semanticAuthorityChangedByProfiler ≡ false
    profilerDoesNotDisableTriggers : triggersDisabled ≡ false
    profilerDoesNotReplaceFunctions : functionsReplaced ≡ false

open SentenceCloseKernelProfileReceipt public

------------------------------------------------------------------------
-- Optimization admission remains measurement-directed.
------------------------------------------------------------------------

data ProfilingRankImpliesSemanticIrrelevance : Set where
data ExpensiveKernelMayBeDisabledWithoutParity : Set where
data UnmeasuredKernelMayBePromotedByGuess : Set where

profileRankDoesNotProveSemanticIrrelevance :
  ProfilingRankImpliesSemanticIrrelevance → ⊥
profileRankDoesNotProveSemanticIrrelevance ()

expensiveKernelStillRequiresParity :
  ExpensiveKernelMayBeDisabledWithoutParity → ⊥
expensiveKernelStillRequiresParity ()

optimizationMustFollowMeasuredKernel :
  UnmeasuredKernelMayBePromotedByGuess → ⊥
optimizationMustFollowMeasuredKernel ()

canonicalProfilerReceipt : SentenceCloseKernelProfileReceipt
canonicalProfilerReceipt =
  sentenceCloseKernelProfileReceipt zero zero false false false refl refl refl refl
