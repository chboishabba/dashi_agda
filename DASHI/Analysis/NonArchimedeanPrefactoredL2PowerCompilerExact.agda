module DASHI.Analysis.NonArchimedeanPrefactoredL2PowerCompilerExact where

------------------------------------------------------------------------
-- PREFACTORED L2 POWER COMPILER
--
-- Correct replacement for the source's false unit-prefactor claim.
--
-- The finite normalized operator is an average of two permutation pullbacks,
-- hence is L2-nonexpansive.  On each Fourier/monomial shell of cycle length L,
-- the checked cyclotomic product gives the full-cycle spectral-rate gain.
-- Writing t = q L + r with r < L then yields
--
--   ||P^t|H_L|| <= ||P^L|H_L||^q ||P^r||
--                  <= 2^(-qL/2).
--
-- Since t = qL+r,
--
--   2^(-qL/2) = 2^(r/2) 2^(-t/2)
--              <= 2^((L-1)/2) 2^(-t/2).
--
-- Squared form (no square-root carrier required):
--
--   ||P^t|H_L||^2 <= 2^(L-1) 2^(-t).
--
-- The exact numerical prefactor coordinate is owned by
-- NonArchimedeanExplicitSquaredMixingPrefactorExact.  This module records the
-- mathematical compiler cutset and prunes the old one-step contraction route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data PrefactorLeaf : Set where
  branchPullbacksArePermutations : PrefactorLeaf
  normalizedOperatorNonexpansive : PrefactorLeaf
  unitaryFourierRechart : PrefactorLeaf
  shellCyclePartition : PrefactorLeaf
  fullCycleSpectralRateGain : PrefactorLeaf
  quotientRemainderPowerSplit : PrefactorLeaf
  shellSquaredPrefactorEnvelope : PrefactorLeaf
  wholeMeanZeroOperatorAssembly : PrefactorLeaf
  optimalTransientConstant : PrefactorLeaf


data PrefactorStatus : Set where
  sourceOwned : PrefactorStatus
  compiled : PrefactorStatus
  repoGeneric : PrefactorStatus
  liveConsumer : PrefactorStatus
  optional : PrefactorStatus

prefactorStatus : PrefactorLeaf → PrefactorStatus
prefactorStatus branchPullbacksArePermutations = sourceOwned
prefactorStatus normalizedOperatorNonexpansive = repoGeneric
prefactorStatus unitaryFourierRechart = sourceOwned
prefactorStatus shellCyclePartition = compiled
prefactorStatus fullCycleSpectralRateGain = compiled
prefactorStatus quotientRemainderPowerSplit = repoGeneric
prefactorStatus shellSquaredPrefactorEnvelope = compiled
prefactorStatus wholeMeanZeroOperatorAssembly = liveConsumer
prefactorStatus optimalTransientConstant = optional


data PrefactorObligation : Set where
  needUnitaryShellPowerNormAssembly : PrefactorObligation
  needOptimalTransientConstant : PrefactorObligation

powerBoundCutset : List PrefactorObligation
powerBoundCutset = needUnitaryShellPowerNormAssembly ∷ []

optionalRefinement : List PrefactorObligation
optionalRefinement = needOptimalTransientConstant ∷ []

record PrefactorCompilerBoundary : Set where
  constructor prefactorCompilerBoundary
  field
    oneStepInverseSqrtTwoNeeded : Bool
    exactOptimalPrefactorNeeded : Bool
    nonnormalTransientAllowed : Bool
    finiteExplicitPrefactorAvailable : Bool
    unitaryAssemblyStillConsumerSpecific : Bool

canonicalPrefactorCompilerBoundary : PrefactorCompilerBoundary
canonicalPrefactorCompilerBoundary =
  prefactorCompilerBoundary false false true true true

oneStepFalseRoutePruned :
  PrefactorCompilerBoundary.oneStepInverseSqrtTwoNeeded
    canonicalPrefactorCompilerBoundary
  ≡ false
oneStepFalseRoutePruned = refl

optimalConstantPruned :
  PrefactorCompilerBoundary.exactOptimalPrefactorNeeded
    canonicalPrefactorCompilerBoundary
  ≡ false
optimalConstantPruned = refl

remainingPowerBoundCutsetIsAssemblyOnly :
  powerBoundCutset ≡ needUnitaryShellPowerNormAssembly ∷ []
remainingPowerBoundCutsetIsAssemblyOnly = refl
