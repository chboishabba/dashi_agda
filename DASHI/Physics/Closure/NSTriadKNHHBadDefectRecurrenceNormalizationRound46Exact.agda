module DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact where

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
-- Round 45 identified C_q as the scale-neutral HH-bad observable.  This file
-- proves the exact normalization suggested by the physical defect programme.
-- If B_q is the time-integrated directional-defect rate and
--
--   B_(q+1) <= (alpha/2) B_q + delta 2^(-(q+1)) beta,
--
-- then
--
--   C_q := delta^(-1) 2^q B_q
--
-- obeys
--
--   C_(q+1) <= alpha C_q + beta.
--
-- The factor 1/2 is therefore exactly the contraction needed to compensate
-- the next dyadic normalization.  No PDE recurrence is asserted here: the
-- theorem says precisely what one-shell physical defect transfer would close
-- the normalized-profile lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans; cong; cong₂)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale

record PhysicalDefectShellRecurrence
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    defectRate : Nat → ℚ
    alpha beta : ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta

    oneShellDefectTransfer : ∀ q →
      defectRate (suc q)
      ≤ alpha * Sharp.half * defectRate q
        + Threshold.threshold parameter
          * Sharp.inverseDyadicScale (suc q) * beta

open PhysicalDefectShellRecurrence public

normalizedDefectProfile :
  ∀ {parameter} →
  PhysicalDefectShellRecurrence parameter → Nat → ℚ
normalizedDefectProfile {parameter} recurrence q =
  Threshold.thresholdInverse parameter
    * Sharp.dyadicScale q
    * defectRate recurrence q

normalizationFactor :
  ∀ {parameter} →
  PhysicalDefectShellRecurrence parameter → Nat → ℚ
normalizationFactor {parameter} recurrence q =
  Threshold.thresholdInverse parameter * Sharp.dyadicScale q

normalizationFactorNonnegative :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  0ℚ ≤ normalizationFactor recurrence q
normalizationFactorNonnegative {parameter} recurrence q =
  let
    instance
      inverseNNI = nonNegative (Threshold.thresholdInverseNonnegative parameter)
      scaleNNI = nonNegative (Scale.dyadicScaleNonnegative q)
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse parameter)
          (Sharp.dyadicScale q)
  in
  ℚP.nonNegative⁻¹ (normalizationFactor recurrence q)

normalizedFirstTermIdentity :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  normalizationFactor recurrence (suc q)
    * (alpha recurrence * Sharp.half * defectRate recurrence q)
  ≡ alpha recurrence * normalizedDefectProfile recurrence q
normalizedFirstTermIdentity {parameter} recurrence q =
  solve
    ( Threshold.thresholdInverse parameter
    ∷ Sharp.dyadicScale q
    ∷ alpha recurrence
    ∷ defectRate recurrence q
    ∷ [])

normalizedForcingIdentity :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  normalizationFactor recurrence (suc q)
    * (Threshold.threshold parameter
      * Sharp.inverseDyadicScale (suc q)
      * beta recurrence)
  ≡ beta recurrence
normalizedForcingIdentity {parameter} recurrence q =
  let
    inverse = Threshold.thresholdInverse parameter
    threshold = Threshold.threshold parameter
    dyadic = Sharp.dyadicScale (suc q)
    inverseDyadic = Sharp.inverseDyadicScale (suc q)
    forcing = beta recurrence

    regroup :
      (inverse * dyadic)
        * (threshold * inverseDyadic * forcing)
      ≡ (inverse * threshold) * (inverseDyadic * dyadic) * forcing
    regroup = solve (inverse ∷ threshold ∷ dyadic ∷ inverseDyadic ∷ forcing ∷ [])

    cancelThreshold :
      (inverse * threshold) * (inverseDyadic * dyadic) * forcing
      ≡ 1ℚ * (inverseDyadic * dyadic) * forcing
    cancelThreshold =
      cong (λ product → product * (inverseDyadic * dyadic) * forcing)
        (Threshold.inverseMeaning parameter)

    cancelDyadic :
      1ℚ * (inverseDyadic * dyadic) * forcing
      ≡ 1ℚ * 1ℚ * forcing
    cancelDyadic =
      cong (λ product → 1ℚ * product * forcing)
        (Sharp.inverseDyadicReciprocal (suc q))

    finish : 1ℚ * 1ℚ * forcing ≡ forcing
    finish = solve (forcing ∷ [])
  in
  trans regroup (trans cancelThreshold (trans cancelDyadic finish))

normalizedDefectRecurrence :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  normalizedDefectProfile recurrence (suc q)
  ≤ alpha recurrence * normalizedDefectProfile recurrence q
    + beta recurrence
normalizedDefectRecurrence {parameter} recurrence q =
  let
    factor = normalizationFactor recurrence (suc q)
    factorNN = normalizationFactorNonnegative recurrence (suc q)

    scaled :
      factor * defectRate recurrence (suc q)
      ≤ factor
        * (alpha recurrence * Sharp.half * defectRate recurrence q
          + Threshold.threshold parameter
            * Sharp.inverseDyadicScale (suc q) * beta recurrence)
    scaled =
      let instance factorNNI = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg factor
        (oneShellDefectTransfer recurrence q)

    leftMeaning :
      factor * defectRate recurrence (suc q)
      ≡ normalizedDefectProfile recurrence (suc q)
    leftMeaning = refl

    distribute :
      factor
        * (alpha recurrence * Sharp.half * defectRate recurrence q
          + Threshold.threshold parameter
            * Sharp.inverseDyadicScale (suc q) * beta recurrence)
      ≡
      factor * (alpha recurrence * Sharp.half * defectRate recurrence q)
      + factor * (Threshold.threshold parameter
        * Sharp.inverseDyadicScale (suc q) * beta recurrence)
    distribute = solve
      ( factor
      ∷ alpha recurrence
      ∷ defectRate recurrence q
      ∷ Threshold.threshold parameter
      ∷ Sharp.inverseDyadicScale (suc q)
      ∷ beta recurrence
      ∷ [])

    rhsIdentity :
      factor
        * (alpha recurrence * Sharp.half * defectRate recurrence q
          + Threshold.threshold parameter
            * Sharp.inverseDyadicScale (suc q) * beta recurrence)
      ≡ alpha recurrence * normalizedDefectProfile recurrence q
        + beta recurrence
    rhsIdentity =
      trans distribute
        (cong₂ _+_
          (normalizedFirstTermIdentity recurrence q)
          (normalizedForcingIdentity recurrence q))
  in
  subst
    (λ left → left
      ≤ alpha recurrence * normalizedDefectProfile recurrence q
        + beta recurrence)
    leftMeaning
    (subst
      (λ right → factor * defectRate recurrence (suc q) ≤ right)
      rhsIdentity
      scaled)

hhBadDefectRecurrenceNormalizationClosed : Bool
hhBadDefectRecurrenceNormalizationClosed = true

hhBadDefectRecurrenceNormalizationClosedIsTrue :
  hhBadDefectRecurrenceNormalizationClosed ≡ true
hhBadDefectRecurrenceNormalizationClosedIsTrue = refl
