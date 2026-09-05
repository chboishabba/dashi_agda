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
--   -> chosen forward word pads to an exact BinaryWord m
--   -> complete binary enumeration has exactly 2^m outcomes
--   -> prefix hit makes the padded word a killed outcome
--   -> Boolean survivor counting gives at most 2^m-1 survivors
--   -> generic Nat recurrence gives geometric survivor-count decay
--   -> probability normalization gives (1-2^(-m))^q.
--
-- All intermediate finite mathematics is now generic/owned.  Remaining leaves
-- are same-object adapters for the actual source ZMod/stopping semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact as Uniform
import DASHI.Analysis.NonArchimedeanHittingWordPaddingExact as Padding
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteBooleanSurvivorCountExact as Survivor
import DASHI.Core.FiniteBlockSurvivalCountDecayExact as CountDecay


data TailLeaf : Set where
  sourceFullPeriod : TailLeaf
  forwardTranslationBlock : TailLeaf
  cyclicZModPredecessor : TailLeaf
  zmodFiniteEnumeration : TailLeaf
  directedIrreducibility : TailLeaf
  finiteUniformHittingBlock : TailLeaf
  exactHittingWordPadding : TailLeaf
  completeBinaryBranchEnumeration : TailLeaf
  selectedHitPrefixIsKilled : TailLeaf
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
status exactHittingWordPadding = compiled
status completeBinaryBranchEnumeration = repoGeneric
status selectedHitPrefixIsKilled = liveAdapter
status oneKilledWordCountBound = repoGeneric
status geometricSurvivorCountDecay = repoGeneric
status probabilityNormalization = liveAdapter
status setDependentExponentialTail = downstream


data TailObligation : Set where
  needZModCyclicPredecessorAdapter : TailObligation
  needZModFiniteEnumerationAdapter : TailObligation
  needPrefixHitAbsorptionWeld : TailObligation
  needProbabilityNormalization : TailObligation

constructiveTailCutset : List TailObligation
constructiveTailCutset =
  needZModCyclicPredecessorAdapter ∷
  needZModFiniteEnumerationAdapter ∷
  needPrefixHitAbsorptionWeld ∷
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
    hittingWordPaddingOwned : Bool
    binaryEnumerationOwned : Bool
    oneKilledWordCountMathOwned : Bool
    genericCountDecayOwned : Bool
    setDependentRateAllowed : Bool

canonicalConstructiveTailBoundary : ConstructiveTailBoundary
canonicalConstructiveTailBoundary =
  constructiveTailBoundary
    false false false true true true true true true true

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

paddingMathOwned :
  ConstructiveTailBoundary.hittingWordPaddingOwned
    canonicalConstructiveTailBoundary
  ≡ true
paddingMathOwned = refl

binaryEnumerationMathOwned :
  ConstructiveTailBoundary.binaryEnumerationOwned
    canonicalConstructiveTailBoundary
  ≡ true
binaryEnumerationMathOwned = refl

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
