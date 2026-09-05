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
--   -> finite state space gives one uniform hitting-block length m for fixed A
--   -> at least one of the 2^m words is killed from every survivor
--   -> S(q+1) <= (2^m-1) S(q)
--   -> S(q) <= (2^m-1)^q S(0)
--   -> P(T>qm) <= (1-2^(-m))^q.
--
-- No principal-submatrix interlacing or normality assumption is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Core.FiniteBlockSurvivalCountDecayExact as CountDecay


data TailLeaf : Set where
  sourceFullPeriod : TailLeaf
  forwardTranslationBlock : TailLeaf
  cyclicZModPredecessor : TailLeaf
  directedIrreducibility : TailLeaf
  finiteUniformHittingBlock : TailLeaf
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
status directedIrreducibility = downstream
status finiteUniformHittingBlock = downstream
status oneKilledWordCountBound = liveAdapter
status geometricSurvivorCountDecay = repoGeneric
status probabilityNormalization = liveAdapter
status setDependentExponentialTail = downstream


data TailObligation : Set where
  needZModCyclicPredecessorAdapter : TailObligation
  needFiniteUniformHittingBlockCompiler : TailObligation
  needOneKilledWordCountBound : TailObligation
  needProbabilityNormalization : TailObligation

constructiveTailCutset : List TailObligation
constructiveTailCutset =
  needZModCyclicPredecessorAdapter ∷
  needFiniteUniformHittingBlockCompiler ∷
  needOneKilledWordCountBound ∷
  needProbabilityNormalization ∷
  []

record ConstructiveTailBoundary : Set where
  constructor constructiveTailBoundary
  field
    sourceUniversalRateStillUsed : Bool
    killedKernelSpectralRadiusNeeded : Bool
    principalSubmatrixInterlacingNeeded : Bool
    sourceFullPeriodReused : Bool
    genericCountDecayOwned : Bool
    setDependentRateAllowed : Bool

canonicalConstructiveTailBoundary : ConstructiveTailBoundary
canonicalConstructiveTailBoundary =
  constructiveTailBoundary false false false true true true

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

constructiveSetDependentRouteLive :
  ConstructiveTailBoundary.setDependentRateAllowed
    canonicalConstructiveTailBoundary
  ≡ true
constructiveSetDependentRouteLive = refl
