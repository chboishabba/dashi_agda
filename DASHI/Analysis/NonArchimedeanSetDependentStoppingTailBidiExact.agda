module DASHI.Analysis.NonArchimedeanSetDependentStoppingTailBidiExact where

------------------------------------------------------------------------
-- SET-DEPENDENT STOPPING-TAIL BIDI
--
-- Repair target after the exact n=3 refutation of the source's universal
-- inverse-sqrt-two survival bound.
--
-- Constructive route:
--
--   checked 3^L=1
--   -> forward block a^(L-1);b is x -> x-1
--   -> directed reachability on Z/2^nZ
--   -> finite witness maximum gives one uniform hitting-block length m
--   -> selected hitting word occurs among the 2^m continuations
--   -> Boolean survivor counting gives at most 2^m-1 survivors
--   -> generic Nat recurrence gives geometric survivor-count decay
--   -> probability normalization gives (1-2^(-m))^q.
--
-- The generic finite mathematics is now owned.  Remaining leaves are concrete
-- same-object adapters for the source ZMod carrier / branch-word enumeration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact as Uniform
import DASHI.Core.FiniteBooleanSurvivorCountExact as Survivor
import DASHI.Core.FiniteBlockSurvivalCountDecayExact as CountDecay


data TailLeaf : Set where
  sourceFullPeriod : TailLeaf
  forwardTranslationBlock : TailLeaf
  cyclicZModPredecessor : TailLeaf
  zmodFiniteEnumeration : TailLeaf
  directedIrreducibility : TailLeaf
  finiteUniformHittingBlock : TailLeaf
  branchWordEnumeration : TailLeaf
  selectedHitWordAppearsKilled : TailLeaf
  oneKilledWordCountBound : TailLeaf
  geometricSurvivorCountDecay : TailLeaf
  probabilityNormalization : TailLeaf
  setDependentExponentialTail : TailLeaf


data TailStatus : Set where
  sourceOwned : TailStatus
  compiled : TailStatus
  repoGeneric : TailStatus
  liveAdapter : TailStatus
  downstream : TailStatus

status : TailLeaf → TailStatus
status sourceFullPeriod = sourceOwned
status forwardTranslationBlock = compiled
status cyclicZModPredecessor = liveAdapter
status zmodFiniteEnumeration = liveAdapter
status directedIrreducibility = downstream
status finiteUniformHittingBlock = repoGeneric
status branchWordEnumeration = liveAdapter
status selectedHitWordAppearsKilled = liveAdapter
status oneKilledWordCountBound = repoGeneric
status geometricSurvivorCountDecay = repoGeneric
status probabilityNormalization = liveAdapter
status setDependentExponentialTail = downstream


data TailObligation : Set where
  needZModCyclicPredecessorAdapter : TailObligation
  needZModFiniteEnumerationAdapter : TailObligation
  needBinaryBranchWordEnumeration : TailObligation
  needChosenHitWordKilledMembership : TailObligation
  needProbabilityNormalization : TailObligation

constructiveTailCutset : List TailObligation
constructiveTailCutset =
  needZModCyclicPredecessorAdapter ∷
  needZModFiniteEnumerationAdapter ∷
  needBinaryBranchWordEnumeration ∷
  needChosenHitWordKilledMembership ∷
  needProbabilityNormalization ∷
  []

record ConstructiveTailBoundary : Set where
  constructor constructiveTailBoundary
  field
    sourceUniversalRateStillUsed : Bool
    killedKernelSpectralRadiusNeeded : Bool
    principalSubmatrixInterlacingNeeded : Bool
    sourceFullPeriodReused : Bool
    uniformWitnessMaximumOwned : Bool
    oneKilledWordCountMathOwned : Bool
    genericCountDecayOwned : Bool
    setDependentRateAllowed : Bool

canonicalConstructiveTailBoundary : ConstructiveTailBoundary
canonicalConstructiveTailBoundary =
  constructiveTailBoundary false false false true true true true true

universalFalseRatePruned :
  ConstructiveTailBoundary.sourceUniversalRateStillUsed
    canonicalConstructiveTailBoundary
  ≡ false
universalFalseRatePruned = refl

killedKernelSpectrumPruned :
  ConstructiveTailBoundary.killedKernelSpectralRadiusNeeded
    canonicalConstructiveTailBoundary
  ≡ false
killedKernelSpectrumPruned = refl

uniformBlockMathOwned :
  ConstructiveTailBoundary.uniformWitnessMaximumOwned
    canonicalConstructiveTailBoundary
  ≡ true
uniformBlockMathOwned = refl

oneKilledWordCountMathOwned :
  ConstructiveTailBoundary.oneKilledWordCountMathOwned
    canonicalConstructiveTailBoundary
  ≡ true
oneKilledWordCountMathOwned = refl

constructiveSetDependentRouteLive :
  ConstructiveTailBoundary.setDependentRateAllowed
    canonicalConstructiveTailBoundary
  ≡ true
constructiveSetDependentRouteLive = refl
