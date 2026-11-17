module DASHI.Analysis.CollatzSyracuseSamplingPushforwardExact where

------------------------------------------------------------------------
-- EXPLICIT STARTING-INTEGER SAMPLING -> PARITY CYLINDERS
--
-- Probability enters here, and nowhere earlier.  Complete 2^m blocks and
-- leftover blocks are separate theorem fields so boundary error cannot vanish
-- by notation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

record FiniteIntervalSampling : Set where
  constructor finiteIntervalSampling
  field
    first : Nat
    length : Nat

open FiniteIntervalSampling public

record SamplingPushforwardSource
    (cylinders : Cylinder.ParityCylinderSource) : Set₁ where
  field
    completeBlockExactUniform :
      (m : Nat) →
      (sample : FiniteIntervalSampling) → Set

    leftoverCount :
      (m : Nat) →
      (sample : FiniteIntervalSampling) → Nat

    leftoverCountBound :
      (m : Nat) →
      (sample : FiniteIntervalSampling) → Set

    finiteTVNumeratorBound :
      (m : Nat) →
      (sample : FiniteIntervalSampling) → Set

open SamplingPushforwardSource public

record SamplingBoundary : Set where
  constructor samplingBoundary
  field
    probabilityBeforeSamplingLaw : Nat
    completeBlocksExactlyUniform : Nat
    incompleteBlocksNeedErrorTerm : Nat
    logarithmicWeightingSameAsUniformInterval : Nat

canonicalSamplingBoundary : SamplingBoundary
canonicalSamplingBoundary = samplingBoundary 0 1 1 0
