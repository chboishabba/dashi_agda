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
-- The source itself already enumerates the literal ZMod (2^n) carrier through
-- Finset.univ, so finite-state enumeration is source-paid. Remaining leaves are
-- predecessor cyclicity, the same-object rw_path/prefix absorption weld, and
-- probability normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact as Uniform
import DASHI.Analysis.NonArchimedeanHittingWordPaddingExact as Padding
import DASHI.Analysis.NonArchimedeanZModStoppingCarrierSourceExact as SourceCarrier
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteBooleanSurvivorCountExact as Survivor
import DASHI.Core.FiniteBlockSurvivalCountDecayExact as CountDecay
import DASHI.Core.FinitePrefixAbsorptionExact as PrefixAbsorption


data TailLeaf : Set where
  sourceFullPeriod : TailLeaf
  sourceZModFiniteEnumeration : TailLeaf
  sourceFiniteBinaryChoiceEnumeration : TailLeaf
  forwardTranslationBlock : TailLeaf
  cyclicZModPredecessor : TailLeaf
  directedIrreducibility : TailLeaf
  finiteUniformHittingBlock : TailLeaf
  exactHittingWordPadding : TailLeaf
  completeBinaryBranchEnumeration : TailLeaf
  genericPrefixAbsorption : TailLeaf
  sourceRwPathPrefixWeld : TailLeaf
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
status sourceZModFiniteEnumeration = sourceOwned
status sourceFiniteBinaryChoiceEnumeration = sourceOwned
status forwardTranslationBlock = compiled
status cyclicZModPredecessor = liveAdapter
status directedIrreducibility = downstream
status finiteUniformHittingBlock = repoGeneric
status exactHittingWordPadding = compiled
status completeBinaryBranchEnumeration = repoGeneric
status genericPrefixAbsorption = repoGeneric
status sourceRwPathPrefixWeld = liveAdapter
status oneKilledWordCountBound = repoGeneric
status geometricSurvivorCountDecay = repoGeneric
status probabilityNormalization = liveAdapter
status setDependentExponentialTail = downstream


data TailObligation : Set where
  needZModCyclicPredecessorAdapter : TailObligation
  needSourceRwPathPrefixAbsorptionWeld : TailObligation
  needProbabilityNormalization : TailObligation

constructiveTailCutset : List TailObligation
constructiveTailCutset =
  needZModCyclicPredecessorAdapter ∷
  needSourceRwPathPrefixAbsorptionWeld ∷
  needProbabilityNormalization ∷
  []

record ConstructiveTailBoundary : Set where
  constructor constructiveTailBoundary
  field
    sourceUniversalRateStillUsed : Bool
    killedKernelSpectralRadiusNeeded : Bool
    principalSubmatrixInterlacingNeeded : Bool
    sourceFullPeriodReused : Bool
    sourceFiniteCarrierEnumerationOwned : Bool
    uniformWitnessMaximumOwned : Bool
    hittingWordPaddingOwned : Bool
    binaryEnumerationOwned : Bool
    genericPrefixAbsorptionOwned : Bool
    oneKilledWordCountMathOwned : Bool
    genericCountDecayOwned : Bool
    setDependentRateAllowed : Bool

canonicalConstructiveTailBoundary : ConstructiveTailBoundary
canonicalConstructiveTailBoundary =
  constructiveTailBoundary
    false false false true true true true true true true true true

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

sourceFiniteCarrierEnumerationClosed :
  ConstructiveTailBoundary.sourceFiniteCarrierEnumerationOwned
    canonicalConstructiveTailBoundary
  ≡ true
sourceFiniteCarrierEnumerationClosed = refl

uniformBlockMathOwned :
  ConstructiveTailBoundary.uniformWitnessMaximumOwned
    canonicalConstructiveTailBoundary
  ≡ true
uniformBlockMathOwned = refl

prefixAbsorptionMathOwned :
  ConstructiveTailBoundary.genericPrefixAbsorptionOwned
    canonicalConstructiveTailBoundary
  ≡ true
prefixAbsorptionMathOwned = refl

constructiveSetDependentRouteLive :
  ConstructiveTailBoundary.setDependentRateAllowed
    canonicalConstructiveTailBoundary
  ≡ true
constructiveSetDependentRouteLive = refl
