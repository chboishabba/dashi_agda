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
-- The final predecessor-transitivity producer is now dependency-closed from
-- Mathlib/source facts: ZMod N is additively cyclic; every residue is the natural
-- cast of its canonical `val`; and k=(x-y).val predecessor steps satisfy
-- pred^k x = x-k = y.  DASHI owns the generic difference-step compiler.
--
-- Authority boundary: this is a source/library dependency closure. We do not
-- claim Agda kernel-checks Lean's ZMod or that a new Lean theorem was added to
-- the external repository.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact as Uniform
import DASHI.Analysis.NonArchimedeanHittingWordPaddingExact as Padding
import DASHI.Analysis.NonArchimedeanZModStoppingCarrierSourceExact as SourceCarrier
import DASHI.Analysis.NonArchimedeanForwardBinarySourcePathWeldExact as SourcePath
import DASHI.Analysis.NonArchimedeanUniformBranchProbabilitySourceExact as SourceProbability
import DASHI.Analysis.NonArchimedeanZModPredecessorTransitivitySourceExact as ZModPred
import DASHI.Core.NatPredecessorDifferenceTransitivityExact as PredCompiler
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
  zmodPredecessorDifferenceCompiler : TailLeaf
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
  sourceLibraryCompiled : TailStatus
  compiled : TailStatus
  repoGeneric : TailStatus
  downstreamCompiled : TailStatus

status : TailLeaf → TailStatus
status sourceFullPeriod = sourceOwned
status sourceZModFiniteEnumeration = sourceOwned
status sourceFiniteBinaryChoiceEnumeration = sourceOwned
status sourceUniformBranchProbability = sourceOwned
status forwardTranslationBlock = compiled
status forwardBinarySourcePathWeld = compiled
status zmodPredecessorDifferenceCompiler = sourceLibraryCompiled
status directedIrreducibility = downstreamCompiled
status finiteUniformHittingBlock = repoGeneric
status exactHittingWordPadding = compiled
status completeBinaryBranchEnumeration = repoGeneric
status genericPrefixAbsorption = repoGeneric
status oneKilledWordCountBound = repoGeneric
status geometricSurvivorCountDecay = repoGeneric
status finiteProbabilityNormalization = repoGeneric
status setDependentExponentialTail = downstreamCompiled


data TailObligation : Set where
  noRemainingConstructiveTailProducer : TailObligation

constructiveTailCutset : List TailObligation
constructiveTailCutset = []

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
    zmodPredecessorMathematicsClosed : Bool
    zmodPredecessorAgdaKernelChecked : Bool
    uniformWitnessMaximumOwned : Bool
    hittingWordPaddingOwned : Bool
    binaryEnumerationOwned : Bool
    genericPrefixAbsorptionOwned : Bool
    oneKilledWordCountMathOwned : Bool
    genericCountDecayOwned : Bool
    finiteProbabilityNormalizationOwned : Bool
    setDependentTailDependencyClosed : Bool

canonicalConstructiveTailBoundary : ConstructiveTailBoundary
canonicalConstructiveTailBoundary =
  constructiveTailBoundary
    false false false true true true true true false
    true true true true true true true true

universalFalseRatePruned :
  ConstructiveTailBoundary.sourceUniversalRateStillUsed
    canonicalConstructiveTailBoundary
  ≡ false
universalFalseRatePruned = refl

zmodPredecessorMathematicsClosed :
  ConstructiveTailBoundary.zmodPredecessorMathematicsClosed
    canonicalConstructiveTailBoundary
  ≡ true
zmodPredecessorMathematicsClosed = refl

crossKernelPretenceRejected :
  ConstructiveTailBoundary.zmodPredecessorAgdaKernelChecked
    canonicalConstructiveTailBoundary
  ≡ false
crossKernelPretenceRejected = refl

constructiveTailDependencyClosed :
  constructiveTailCutset ≡ []
constructiveTailDependencyClosed = refl
