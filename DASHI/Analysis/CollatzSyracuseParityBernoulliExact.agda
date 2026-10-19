module DASHI.Analysis.CollatzSyracuseParityBernoulliExact where

------------------------------------------------------------------------
-- DIRECT BERNOULLI ROUTE FROM EXACT PARITY-CYLINDER UNIFORMITY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteUniformBijectionTransportExact as Uniform
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.Analysis.CollatzSyracuseCompleteBlockBijectionExact as Block
import DASHI.Analysis.CollatzSyracuseSamplingPushforwardExact as Sampling

ones : {m : Nat} → Binary.BinaryWord m → Nat
ones Binary.end = zero
ones (Binary.bit0 tail) = ones tail
ones (Binary.bit1 tail) = suc (ones tail)

zeros : {m : Nat} → Binary.BinaryWord m → Nat
zeros Binary.end = zero
zeros (Binary.bit0 tail) = suc (zeros tail)
zeros (Binary.bit1 tail) = zeros tail

wordLengthSplit :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  zeros word + ones word ≡ m
wordLengthSplit Binary.end = refl
wordLengthSplit (Binary.bit0 tail)
  rewrite wordLengthSplit tail = refl
wordLengthSplit (Binary.bit1 tail)
  rewrite wordLengthSplit tail = refl

record UniformParityWordLaw (m : Nat) : Set₁ where
  field
    wordMassNumerator : Binary.BinaryWord m → Nat
    commonMassNumerator : Nat
    everyWordSameMass :
      (word : Binary.BinaryWord m) →
      wordMassNumerator word ≡ commonMassNumerator
    totalOutcomeCount : Nat
    totalOutcomeCountIsPow2 :
      totalOutcomeCount ≡ Binary.pow2Count m

open UniformParityWordLaw public

uniformMassToParityWordLaw :
  {m : Nat} →
  Uniform.UniformNatMass (Binary.BinaryWord m) →
  UniformParityWordLaw m
uniformMassToParityWordLaw {m} mass = record
  { wordMassNumerator = Uniform.mass mass
  ; commonMassNumerator = Uniform.commonMass mass
  ; everyWordSameMass = Uniform.uniform mass
  ; totalOutcomeCount = Binary.pow2Count m
  ; totalOutcomeCountIsPow2 = refl
  }

canonicalCompleteBlockParityWordLaw :
  (m : Nat) →
  UniformParityWordLaw m
canonicalCompleteBlockParityWordLaw m =
  uniformMassToParityWordLaw
    (Block.canonicalCompleteBlockUniformWordMass m)

------------------------------------------------------------------------
-- The older sampling socket remains for arbitrary interval/log-weighted laws.
-- Complete 2^m blocks no longer require this producer: their uniform law is
-- constructed above from the literal same-object cylinder bijection.
------------------------------------------------------------------------

record CompleteBlockBernoulliSource : Set₁ where
  field
    cylinders : Cylinder.ParityCylinderSource
    sampling : Sampling.SamplingPushforwardSource cylinders
    level : Nat
    sample : Sampling.FiniteIntervalSampling
    completeBlockWitness :
      Sampling.completeBlockExactUniform sampling level sample
    wordLaw : UniformParityWordLaw level

open CompleteBlockBernoulliSource public

------------------------------------------------------------------------
-- Concentration consumer.
------------------------------------------------------------------------

record BernoulliConcentrationSource (m : Nat) : Set₁ where
  field
    law : UniformParityWordLaw m
    DeviationThreshold : Set
    TailEvent : DeviationThreshold → Binary.BinaryWord m → Set
    Bound : DeviationThreshold → Set
    tailBound :
      (threshold : DeviationThreshold) →
      ((word : Binary.BinaryWord m) →
        TailEvent threshold word → Set) →
      Bound threshold

open BernoulliConcentrationSource public

record ParityBernoulliBoundary : Set where
  constructor parityBernoulliBoundary
  field
    exactCylinderBijectionOwned : Bool
    completeBlockUniformityOwned : Bool
    spectralGapRequired : Bool
    pseudoSpectralGapRequired : Bool
    markovMixingRequired : Bool
    finiteBernoulliTailTheoremRequired : Bool
    arbitraryIntervalNeedsBoundaryError : Bool
    logarithmicSamplingNeedsSeparateTransport : Bool

open ParityBernoulliBoundary public

canonicalParityBernoulliBoundary : ParityBernoulliBoundary
canonicalParityBernoulliBoundary =
  parityBernoulliBoundary
    true true
    false false false
    true true true

spectralGapNotRequiredForCompleteBlockBernoulli :
  spectralGapRequired canonicalParityBernoulliBoundary ≡ false
spectralGapNotRequiredForCompleteBlockBernoulli = refl

mixingNotRequiredForCompleteBlockBernoulli :
  markovMixingRequired canonicalParityBernoulliBoundary ≡ false
mixingNotRequiredForCompleteBlockBernoulli = refl
