module DASHI.Physics.Closure.RealDyadicDecayBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; z≤n)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _*ℝ_
  ; 1ℝ
  ; ≤ℝ-refl
  )

import DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks as Seminorm

------------------------------------------------------------------------
-- Symbolic dyadic-decay to real-valued bridge.
--
-- The Balaban/Q_hp locality arithmetic in repo is symbolic:
--
--   C_local * 2^(-2k)
--
-- This module exposes the missing real-valued interpretation boundary used by
-- the KP small-field survival lane.

postulate
  DyadicRealSemantics :
    Set₁

record DyadicRealSemanticsSocket : Set₁ where
  field
    natAsReal :
      Nat →
      ℝ

    dyadicPow2NegAsReal :
      Nat →
      ℝ

    dyadicPow2NegZeroIsOne :
      dyadicPow2NegAsReal 0 ≡ 1ℝ

    dyadicPow2NegMonotone :
      ∀ {m n : Nat} →
      m ≤ n →
      dyadicPow2NegAsReal n ≤ℝ dyadicPow2NegAsReal m

    perLinkOscillationDecayAsReal :
      ∀ (cLocal k : Nat) →
      dyadicDecayAsReal (Seminorm.perLinkOscillationDecay cLocal k)
        ≤ℝ (natAsReal cLocal *ℝ dyadicPow2NegAsReal (Seminorm.double k))

open DyadicRealSemanticsSocket public

postulate
  currentDyadicRealSemantics :
    DyadicRealSemanticsSocket

natAsReal : Nat → ℝ
natAsReal = DyadicRealSemanticsSocket.natAsReal currentDyadicRealSemantics

dyadicPow2NegAsReal : Nat → ℝ
dyadicPow2NegAsReal =
  DyadicRealSemanticsSocket.dyadicPow2NegAsReal currentDyadicRealSemantics

dyadicDecayAsReal : Seminorm.DyadicDecay → ℝ
dyadicDecayAsReal decay =
  natAsReal (Seminorm.DyadicDecay.coefficient decay)
    *ℝ
  dyadicPow2NegAsReal (Seminorm.DyadicDecay.exponent decay)

dyadicPow2NegZeroIsOne :
  dyadicPow2NegAsReal 0 ≡ 1ℝ
dyadicPow2NegZeroIsOne =
  DyadicRealSemanticsSocket.dyadicPow2NegZeroIsOne currentDyadicRealSemantics

dyadicPow2NegMonotone :
  ∀ {m n : Nat} →
  m ≤ n →
  dyadicPow2NegAsReal n ≤ℝ dyadicPow2NegAsReal m
dyadicPow2NegMonotone =
  DyadicRealSemanticsSocket.dyadicPow2NegMonotone currentDyadicRealSemantics

perLinkOscillationDecayAsReal :
  ∀ (cLocal k : Nat) →
  dyadicDecayAsReal (Seminorm.perLinkOscillationDecay cLocal k)
    ≤ℝ (natAsReal cLocal *ℝ dyadicPow2NegAsReal (Seminorm.double k))
perLinkOscillationDecayAsReal =
  DyadicRealSemanticsSocket.perLinkOscillationDecayAsReal currentDyadicRealSemantics

dyadicPow2NegNonIncreasing :
  ∀ (k : Nat) →
  dyadicPow2NegAsReal (Seminorm.double k)
    ≤ℝ
  dyadicPow2NegAsReal 0
dyadicPow2NegNonIncreasing k =
  dyadicPow2NegMonotone z≤n

dyadicDecayAtZeroIsUnit :
  dyadicDecayAsReal (Seminorm.perLinkOscillationDecay 1 0)
    ≡
  (natAsReal 1 *ℝ 1ℝ)
dyadicDecayAtZeroIsUnit = refl

dyadicDecayBelowUnit :
  ∀ (k : Nat) →
  (1ℝ *ℝ dyadicPow2NegAsReal (Seminorm.double k))
    ≤ℝ
  (1ℝ *ℝ 1ℝ)
dyadicDecayBelowUnit k =
  dyadicPow2NegNonIncreasing k

unitPerLinkDecayBelowScaleZero :
  ∀ (k : Nat) →
  (1ℝ *ℝ dyadicPow2NegAsReal (Seminorm.double k))
    ≤ℝ
  (1ℝ *ℝ dyadicPow2NegAsReal (Seminorm.double 0))
unitPerLinkDecayBelowScaleZero k =
  dyadicDecayBelowUnit k
