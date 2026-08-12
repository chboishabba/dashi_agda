module DASHI.Physics.Closure.NSTriadKNHHBadThresholdUniformityRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The bad-set Markov transfer contributes delta^(-1), while the Round-45
-- physical defect target contributes delta.  These cancel algebraically, but
-- that alone does not prove the normalized profile ceiling is independent of
-- delta.  This file makes the distinction a type.
--
-- `ThresholdIndexedHHBadProfiles` allows the ceiling C_*(delta) to vary with
-- the good/bad threshold.  `ThresholdUniformHHBadProfile` is the stronger
-- physical theorem required to remove delta from the viscosity reserve: one
-- common C_* bounds every threshold-indexed normalized coefficient.
--
-- Thus future proofs cannot silently turn C_*(delta) into C_* merely because
-- the explicit Markov factors cancel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale

record ThresholdIndexedHHBadProfiles : Set₁ where
  field
    normalizedCoefficient : Threshold.PositiveThreshold → Nat → ℚ
    normalizedCoefficientNonnegative : ∀ parameter shell →
      0ℚ ≤ normalizedCoefficient parameter shell

    thresholdCeiling : Threshold.PositiveThreshold → ℚ
    thresholdCeilingNonnegative : ∀ parameter →
      0ℚ ≤ thresholdCeiling parameter

    coefficientBelowThresholdCeiling : ∀ parameter shell →
      normalizedCoefficient parameter shell
      ≤ thresholdCeiling parameter

open ThresholdIndexedHHBadProfiles public

record ThresholdUniformHHBadProfile
    (indexed : ThresholdIndexedHHBadProfiles) : Set where
  field
    commonCeiling : ℚ
    commonCeilingNonnegative : 0ℚ ≤ commonCeiling
    coefficientBelowCommonCeiling : ∀ parameter shell →
      normalizedCoefficient indexed parameter shell ≤ commonCeiling

open ThresholdUniformHHBadProfile public

thresholdIndexedCanonicalEta :
  ThresholdIndexedHHBadProfiles → Threshold.PositiveThreshold → ℚ
thresholdIndexedCanonicalEta indexed parameter =
  Sharp.two * thresholdCeiling indexed parameter

thresholdUniformCanonicalEta :
  ∀ {indexed} → ThresholdUniformHHBadProfile indexed → ℚ
thresholdUniformCanonicalEta uniform =
  Sharp.two * commonCeiling uniform

thresholdUniformCanonicalEtaNonnegative :
  ∀ {indexed} (uniform : ThresholdUniformHHBadProfile indexed) →
  0ℚ ≤ thresholdUniformCanonicalEta uniform
thresholdUniformCanonicalEtaNonnegative uniform =
  let instance
    twoNNI = nonNegative Scale.twoNonnegative
    ceilingNNI = nonNegative (commonCeilingNonnegative uniform)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (commonCeiling uniform)
  in
  ℚP.nonNegative⁻¹ (thresholdUniformCanonicalEta uniform)

record ThresholdCeilingIsActuallyUniform
    (indexed : ThresholdIndexedHHBadProfiles) : Set where
  field
    uniform : ThresholdUniformHHBadProfile indexed
    thresholdCeilingExact : ∀ parameter →
      thresholdCeiling indexed parameter ≡ commonCeiling uniform

open ThresholdCeilingIsActuallyUniform public

indexedEtaEqualsUniformEta :
  ∀ {indexed}
    (proof : ThresholdCeilingIsActuallyUniform indexed)
    parameter →
  thresholdIndexedCanonicalEta indexed parameter
  ≡ thresholdUniformCanonicalEta (uniform proof)
indexedEtaEqualsUniformEta {indexed} proof parameter =
  cong (Sharp.two *_)
    (thresholdCeilingExact proof parameter)

hhBadThresholdDependenceMadeExplicit : Bool
hhBadThresholdDependenceMadeExplicit = true

thresholdUniformPhysicalCeilingConstructed : Bool
thresholdUniformPhysicalCeilingConstructed = false

hhBadThresholdDependenceMadeExplicitIsTrue :
  hhBadThresholdDependenceMadeExplicit ≡ true
hhBadThresholdDependenceMadeExplicitIsTrue = refl

thresholdUniformPhysicalCeilingConstructedIsFalse :
  thresholdUniformPhysicalCeilingConstructed ≡ false
thresholdUniformPhysicalCeilingConstructedIsFalse = refl
