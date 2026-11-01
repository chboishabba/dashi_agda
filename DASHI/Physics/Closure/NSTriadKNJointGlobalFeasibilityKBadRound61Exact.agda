module DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityKBadRound61Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 61 CONTRIBUTION
--
-- Round54/56 proved the exact rational two-resource obstruction with the
-- HH-bad hard tax 2 C_*.  Round61's literal charge bridge shows that the
-- physical tax is in general
--
--       2 C_* K_bad,
--
-- where K_bad is the unmasked-charge multiplicity.  This file propagates that
-- factor through the global necessary condition rather than silently setting
-- K_bad=1 downstream.
--
-- Every feasible soft Young allocation with correction cap B_* and strict
-- viscosity absorption
--
--   2 C_* K_bad + epsilon_total + 1/16 < 1
--
-- necessarily satisfies
--
--   c_total
--     <= (1 - 1/16 - 2 C_* K_bad) B_*.
--
-- If B_*>0 the conclusion is strict.  This is an exact rational no-go and is
-- independent of the particular Round61 equal-third constructive allocator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _<_; _≤_; nonNegative; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Closure.NSTriadKNJointSoftCorrectionBudgetRound54Exact as Joint
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Round54
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

hhBadTax : ℚ → ℚ → ℚ
hhBadTax ceiling multiplicity = Sharp.two * ceiling * multiplicity

viscosityReserve : ℚ → ℚ → ℚ
viscosityReserve ceiling multiplicity =
  1ℚ - Round54.hardFourClassTax - hhBadTax ceiling multiplicity

record KBadJointGlobalFeasibility
    (hhBadCeiling badChargeMultiplicity : ℚ)
    (allocation : Joint.ThreeSoftYoungAllocation) : Set where
  field
    correctionCap : Joint.AggregateSoftCorrectionCap allocation
    hhBadCeilingNonnegative : 0ℚ ≤ hhBadCeiling
    badChargeMultiplicityNonnegative : 0ℚ ≤ badChargeMultiplicity

    strictViscosityGate :
      hhBadTax hhBadCeiling badChargeMultiplicity
        + Joint.softEtaTotal allocation
        + Round54.hardFourClassTax
      < 1ℚ

open KBadJointGlobalFeasibility public

strictGateForcesSoftEtaBelowReserve :
  ∀ {hhBadCeiling badChargeMultiplicity allocation} →
  KBadJointGlobalFeasibility
    hhBadCeiling badChargeMultiplicity allocation →
  Joint.softEtaTotal allocation
  < viscosityReserve hhBadCeiling badChargeMultiplicity
strictGateForcesSoftEtaBelowReserve
    {hhBadCeiling} {badChargeMultiplicity} {allocation} feasible =
  let
    hard = hhBadTax hhBadCeiling badChargeMultiplicity
    boundary = Round54.hardFourClassTax
    soft = Joint.softEtaTotal allocation
    shift = hard + boundary

    shifted :
      (hard + soft + boundary) + (- shift)
      < 1ℚ + (- shift)
    shifted = ℚP.+-monoʳ-< (- shift) (strictViscosityGate feasible)

    leftMeaning :
      (hard + soft + boundary) + (- shift) ≡ soft
    leftMeaning = solve (hard ∷ soft ∷ boundary ∷ [])

    rightMeaning :
      1ℚ + (- shift)
      ≡ viscosityReserve hhBadCeiling badChargeMultiplicity
    rightMeaning = solve
      ( hard
      ∷ boundary
      ∷ hhBadCeiling
      ∷ badChargeMultiplicity
      ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

kBadJointYoungProductKillTest :
  ∀ {hhBadCeiling badChargeMultiplicity allocation}
    (feasible : KBadJointGlobalFeasibility
      hhBadCeiling badChargeMultiplicity allocation) →
  Joint.softNumeratorTotal allocation
  ≤ Joint.softEtaTotal allocation
      * Joint.bCap (correctionCap feasible)
kBadJointYoungProductKillTest feasible =
  Joint.jointYoungKillTest (correctionCap feasible)

kBadRationalTwoResourceNoGo :
  ∀ {hhBadCeiling badChargeMultiplicity allocation}
    (feasible : KBadJointGlobalFeasibility
      hhBadCeiling badChargeMultiplicity allocation) →
  Joint.softNumeratorTotal allocation
  ≤ viscosityReserve hhBadCeiling badChargeMultiplicity
      * Joint.bCap (correctionCap feasible)
kBadRationalTwoResourceNoGo
    {hhBadCeiling} {badChargeMultiplicity} {allocation} feasible =
  let
    cap = correctionCap feasible
    etaBelowReserve = strictGateForcesSoftEtaBelowReserve feasible
    scaled :
      Joint.softEtaTotal allocation * Joint.bCap cap
      ≤ viscosityReserve hhBadCeiling badChargeMultiplicity
          * Joint.bCap cap
    scaled =
      let instance capNN = nonNegative (Joint.bCapNonnegative cap)
      in ℚP.*-monoʳ-≤-nonNeg
        (Joint.bCap cap)
        (ℚP.<⇒≤ etaBelowReserve)
  in
  ℚP.≤-trans
    (kBadJointYoungProductKillTest feasible)
    scaled

kBadRationalTwoResourceNoGoStrictWhenCapPositive :
  ∀ {hhBadCeiling badChargeMultiplicity allocation}
    (feasible : KBadJointGlobalFeasibility
      hhBadCeiling badChargeMultiplicity allocation) →
  0ℚ < Joint.bCap (correctionCap feasible) →
  Joint.softNumeratorTotal allocation
  < viscosityReserve hhBadCeiling badChargeMultiplicity
      * Joint.bCap (correctionCap feasible)
kBadRationalTwoResourceNoGoStrictWhenCapPositive
    {hhBadCeiling} {badChargeMultiplicity} {allocation}
    feasible capPositive =
  let
    cap = correctionCap feasible
    etaStrict = strictGateForcesSoftEtaBelowReserve feasible
    scaledStrict :
      Joint.softEtaTotal allocation * Joint.bCap cap
      < viscosityReserve hhBadCeiling badChargeMultiplicity
          * Joint.bCap cap
    scaledStrict =
      let instance capPos = positive capPositive
      in ℚP.*-monoˡ-<-pos (Joint.bCap cap) etaStrict
  in
  ℚP.≤-<-trans
    (kBadJointYoungProductKillTest feasible)
    scaledStrict

kBadPropagatedThroughGlobalNoGo : Bool
kBadPropagatedThroughGlobalNoGo = true

kBadPropagatedThroughGlobalNoGoIsTrue :
  kBadPropagatedThroughGlobalNoGo ≡ true
kBadPropagatedThroughGlobalNoGoIsTrue = refl
