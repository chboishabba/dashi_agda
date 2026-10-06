module DASHI.Analysis.CollatzSyracuseParityBernoulliExact where

------------------------------------------------------------------------
-- DIRECT BERNOULLI ROUTE FROM EXACT PARITY-CYLINDER UNIFORMITY
--
-- This route deliberately bypasses the unrelated finite 3z/(3z-1) spectral
-- relation.  If a sampled complete 2^m block pushes forward to the uniform law
-- on BinaryWord m, then the m parity coordinates have exactly the finite
-- Bernoulli word law.  Concentration may therefore consume a standard finite
-- Bernoulli tail theorem directly; no spectral gap or mixing coefficient is
-- logically required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
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

------------------------------------------------------------------------
-- Exact uniform word law.  The actual sampling producer is separate so that
-- probability cannot enter the literal dynamics by notation.
------------------------------------------------------------------------

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
--
-- A source theorem may instantiate this with an exact binomial tail, Hoeffding,
-- Chernoff, or another theorem on the genuinely uniform BinaryWord carrier.
-- Unlike the old route, there is no field whose mere name "spectralGap" is
-- permitted to authorize concentration.
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
    exactCylinderBijectionRequired : Bool
    completeBlockUniformityRequired : Bool
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
