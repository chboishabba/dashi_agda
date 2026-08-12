module DASHI.Physics.Closure.NSTriadKNHHBadDefectToNormalizedProfileRound45Exact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 40 proved the directional-defect owner transfer
--
--   delta * G_bad <= Defect,
--   Defect <= B_q * D
--       =>
--   G_bad <= delta^-1 * B_q * D.
--
-- Round 44/45 showed that the true HH-bad target is the dimensionless profile
-- C_q in
--
--   G_bad <= C_q 2^-q D.
--
-- The missing connection is now exact.  If the physical defect rate itself
-- has the inverse-shell form
--
--   B_q <= delta * C_* * 2^-q,
--
-- then the exact threshold inverse cancels delta and Round 40 yields
--
--   G_bad <= C_* 2^-q D.
--
-- Thus the earlier master directional-defect program can directly manufacture
-- the normalized HH-bad profile.  The remaining PDE theorem is sharply stated:
-- prove a cutoff-uniform inverse-shell bound on the *physical time-integrated
-- defect owner rate*.  No extra intermittency functional is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadDefectOwnerScalingRound40Exact as Defect

record InverseShellDefectProfile
    (parameter : Threshold.PositiveThreshold)
    (shell : Nat)
    (rate : Defect.BadDefectOwnerRate parameter) : Set where
  field
    profileCeiling : ℚ
    profileCeilingNonnegative : 0ℚ ≤ profileCeiling

    defectRateBelowThresholdProfileInverseShell :
      Defect.defectRate rate
      ≤ Threshold.threshold parameter
          * profileCeiling
          * Sharp.inverseDyadicScale shell

open InverseShellDefectProfile public

inverseThresholdTimesDefectRateBelowProfileInverseShell :
  ∀ {parameter shell}
    (rate : Defect.BadDefectOwnerRate parameter)
    (profile : InverseShellDefectProfile parameter shell rate) →
  Threshold.thresholdInverse parameter * Defect.defectRate rate
  ≤ profileCeiling profile * Sharp.inverseDyadicScale shell
inverseThresholdTimesDefectRateBelowProfileInverseShell
    {parameter} {shell} rate profile =
  let
    inv = Threshold.thresholdInverse parameter
    delta = Threshold.threshold parameter
    C = profileCeiling profile
    mu = Sharp.inverseDyadicScale shell

    invNN = Threshold.thresholdInverseNonnegative parameter

    scaled :
      inv * Defect.defectRate rate
      ≤ inv * (delta * C * mu)
    scaled =
      let instance invNNI = nonNegative invNN
      in ℚP.*-monoˡ-≤-nonNeg inv
        (defectRateBelowThresholdProfileInverseShell profile)

    rightMeaning : inv * (delta * C * mu) ≡ C * mu
    rightMeaning =
      trans
        (solve (inv ∷ delta ∷ C ∷ mu ∷ []))
        (trans
          (cong (λ product → product * C * mu)
            (Threshold.inverseMeaning parameter))
          (solve (C ∷ mu ∷ [])))
  in
  subst
    (λ upper → inv * Defect.defectRate rate ≤ upper)
    rightMeaning
    scaled

badGainBelowNormalizedProfileTimesDissipation :
  ∀ {parameter shell}
    (rate : Defect.BadDefectOwnerRate parameter)
    (profile : InverseShellDefectProfile parameter shell rate) →
  Defect.badGain rate
  ≤ profileCeiling profile
      * Sharp.inverseDyadicScale shell
      * Defect.dissipation rate
badGainBelowNormalizedProfileTimesDissipation
    {parameter} {shell} rate profile =
  let
    first = Defect.badGainBelowBOverDeltaDissipation rate

    coefficientBound :
      Threshold.thresholdInverse parameter * Defect.defectRate rate
      ≤ profileCeiling profile * Sharp.inverseDyadicScale shell
    coefficientBound =
      inverseThresholdTimesDefectRateBelowProfileInverseShell rate profile

    dissNN = Defect.dissipationNonnegative rate

    scaled :
      (Threshold.thresholdInverse parameter * Defect.defectRate rate)
        * Defect.dissipation rate
      ≤ (profileCeiling profile * Sharp.inverseDyadicScale shell)
        * Defect.dissipation rate
    scaled =
      let instance dissNNI = nonNegative dissNN
      in ℚP.*-monoʳ-≤-nonNeg (Defect.dissipation rate) coefficientBound

    firstMeaning :
      Threshold.thresholdInverse parameter
        * Defect.defectRate rate * Defect.dissipation rate
      ≡ (Threshold.thresholdInverse parameter * Defect.defectRate rate)
        * Defect.dissipation rate
    firstMeaning = solve
      ( Threshold.thresholdInverse parameter
      ∷ Defect.defectRate rate
      ∷ Defect.dissipation rate
      ∷ [])

    endpoint :
      (profileCeiling profile * Sharp.inverseDyadicScale shell)
        * Defect.dissipation rate
      ≡ profileCeiling profile
          * Sharp.inverseDyadicScale shell
          * Defect.dissipation rate
    endpoint = solve
      ( profileCeiling profile
      ∷ Sharp.inverseDyadicScale shell
      ∷ Defect.dissipation rate
      ∷ [])
  in
  ℚP.≤-trans first
    (subst
      (λ lower →
        lower
        ≤ profileCeiling profile * Sharp.inverseDyadicScale shell
          * Defect.dissipation rate)
      (sym firstMeaning)
      (subst
        (λ upper →
          (Threshold.thresholdInverse parameter * Defect.defectRate rate)
            * Defect.dissipation rate
          ≤ upper)
        endpoint
        scaled))

normalizedCoefficientFromDefectProfile :
  ∀ {parameter shell}
    (rate : Defect.BadDefectOwnerRate parameter)
    (profile : InverseShellDefectProfile parameter shell rate) →
  let gainDensity =
        profileCeiling profile * Sharp.inverseDyadicScale shell
  in
  gainDensity * Sharp.dyadicScale shell ≡ profileCeiling profile
normalizedCoefficientFromDefectProfile {shell = shell} rate profile =
  let
    C = profileCeiling profile
    mu = Sharp.inverseDyadicScale shell
    lambda = Sharp.dyadicScale shell
  in
  trans
    (solve (C ∷ mu ∷ lambda ∷ []))
    (trans
      (cong (C *_) (Sharp.inverseDyadicReciprocal shell))
      (solve (C ∷ [])))

hhBadDefectRateProducesNormalizedProfile : Bool
hhBadDefectRateProducesNormalizedProfile = true

hhBadDefectRateProducesNormalizedProfileIsTrue :
  hhBadDefectRateProducesNormalizedProfile ≡ true
hhBadDefectRateProducesNormalizedProfileIsTrue = refl
