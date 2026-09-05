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
--   -> prefix hit makes every padded extension killed
--   -> Boolean survivor counting gives at most 2^m-1 survivors
--   -> generic Nat recurrence gives geometric survivor-count decay
--   -> exact finite-fraction normalization gives ((2^m-1)/2^m)^q.
--
-- Source receipts now own the finite ZMod enumeration, the two affine branch
-- definitions, no edge multiplicity, and P_n=(1/2)D_n. The Forward/Binary weld
-- owns the bit convention explicitly (bit0=true=A, bit1=false=B). Therefore the
-- only remaining constructive tail leaf is the actual cyclic predecessor
-- transitivity adapter for the source ZMod (2^n) carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact as Uniform
import DASHI.Analysis.NonArchimedeanHittingWordPaddingExact as Padding
import DASHI.Analysis.NonArchimedeanZModStoppingCarrierSourceExact as SourceCarrier
import DASHI.Analysis.NonArchimedeanForwardBinarySourcePathWeldExact as SourcePath
import DASHI.Analysis.NonArchimedeanUniformBranchProbabilitySourceExact as SourceProbability
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteBooleanSurvivorCountExact as Survivor
import DASHI.Core.FiniteBlockSurvivalCountDecayExact as CountDecay
import DASHI.Core.FinitePrefixAbsorptionExact as PrefixAbsorption
import DASHI.Core.FiniteUniformProbabilityNormalizationExact as Probability


data TailLeaf : Set where
  sourceFullPeriod : TailLeaf
  sourceZModFiniteEnumeration : TailLeaf
  sourceFiniteBinaryChoiceEnumeration : TailLeaf
  sourceUniformBranchProbability : TailLeaf
  forwardTranslationBlock : TailLeaf
  forwardBinarySourcePathWeld : TailLeaf
  cyclicZModPredecessor : TailLeaf
  directedIrreducibility : TailLeaf
  finiteUniformHittingBlock : TailLeaf
  exactHittingWordPadding : TailLeaf
  completeBinaryBranchEnumeration : TailLeaf
  genericPrefixAbsorption : TailLeaf
  oneKilledWordCountBound : TailLeaf
  geometricSurvivorCountDecay : TailLeaf
  finiteProbabilityNormalization : TailLeaf
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
status sourceUniformBranchProbability = sourceOwned
status forwardTranslationBlock = compiled
status forwardBinarySourcePathWeld = compiled
status cyclicZModPredecessor = liveAdapter
status directedIrreducibility = downstream
status finiteUniformHittingBlock = repoGeneric
status exactHittingWordPadding = compiled
status completeBinaryBranchEnumeration = repoGeneric
status genericPrefixAbsorption = repoGeneric
status oneKilledWordCountBound = repoGeneric
status geometricSurvivorCountDecay = repoGeneric
status finiteProbabilityNormalization = repoGeneric
status setDependentExponentialTail = downstream


data TailObligation : Set where
  needZModCyclicPredecessorAdapter : TailObligation

constructiveTailCutset : List TailObligation
constructiveTailCutset = needZModCyclicPredecessorAdapter ∷ []

record ConstructiveTailBoundary : Set where
  constructor constructiveTailBoundary
  field
    sourceUniversalRateStillUsed : Bool
    killedKernelSpectralRadiusNeeded : Bool
    principalSubmatrixInterlacingNeeded : Bool
    sourceFullPeriodReused : Bool
    sourceFiniteCarrierEnumerationOwned : Bool
    sourceUniformBranchProbabilityOwned : Bool
    forwardBinarySourcePathWeldOwned : Bool
    uniformWitnessMaximumOwned : Bool
    hittingWordPaddingOwned : Bool
    binaryEnumerationOwned : Bool
    genericPrefixAbsorptionOwned : Bool
    oneKilledWordCountMathOwned : Bool
    genericCountDecayOwned : Bool
    finiteProbabilityNormalizationOwned : Bool
    setDependentRateAllowed : Bool

canonicalConstructiveTailBoundary : ConstructiveTailBoundary
canonicalConstructiveTailBoundary =
  constructiveTailBoundary
    false false false true true true true true true true true true true true true

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

sourceProbabilitySemanticsClosed :
  ConstructiveTailBoundary.sourceUniformBranchProbabilityOwned
    canonicalConstructiveTailBoundary
  ≡ true
sourceProbabilitySemanticsClosed = refl

finiteNormalizationClosed :
  ConstructiveTailBoundary.finiteProbabilityNormalizationOwned
    canonicalConstructiveTailBoundary
  ≡ true
finiteNormalizationClosed = refl

constructiveTailHasSingleRemainingLeaf :
  constructiveTailCutset ≡ needZModCyclicPredecessorAdapter ∷ []
constructiveTailHasSingleRemainingLeaf = refl
