module DASHI.Physics.Closure.NSTriadKNHHBadSummableDyadicGainRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Grundlehren der mathematischen Wissenschaften 343, Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 33 proved that the unique exact multiplicative compensation for the
-- raw HH-bad ratio R_q = 2 * 2^q is
--
--   g_q(eta) = (eta / 2) * 2^-q.
--
-- Here we prove the exact finite-prefix summation law
--
--   sum_{q=0}^Q g_q(eta)
--     = eta - eta * 2^-(Q+1),
--
-- hence
--
--   sum_{q=0}^Q g_q(eta) + eta * 2^-(Q+1) = eta.
--
-- Therefore the one inverse dyadic power demanded by the raw Bernstein
-- obstruction is not itself a divergent shell tax: the complete infinite
-- target profile has exact total mass eta.  The physical problem is narrower
-- and sharper -- produce this shell-decaying profile from the trajectory.
--
-- No occupation-time, amplitude, intermittency, or alignment estimate is
-- assumed here.  The module only proves the exact global arithmetic of the
-- uniquely forced target profile.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

requiredGainPrefix : ℚ → Nat → ℚ
requiredGainPrefix eta zero =
  Sharp.requiredHHBadGain eta zero
requiredGainPrefix eta (suc lastShell) =
  requiredGainPrefix eta lastShell
  + Sharp.requiredHHBadGain eta (suc lastShell)

requiredGainPrefixClosedForm :
  ∀ eta lastShell →
  requiredGainPrefix eta lastShell
  ≡ eta - eta * Sharp.inverseDyadicScale (suc lastShell)
requiredGainPrefixClosedForm eta zero =
  ℚRing.solve-∀ eta
requiredGainPrefixClosedForm eta (suc lastShell)
  rewrite requiredGainPrefixClosedForm eta lastShell =
  ℚRing.solve-∀ eta (Sharp.inverseDyadicScale (suc lastShell))

requiredGainPrefixPlusTail :
  ∀ eta lastShell →
  requiredGainPrefix eta lastShell
    + eta * Sharp.inverseDyadicScale (suc lastShell)
  ≡ eta
requiredGainPrefixPlusTail eta lastShell =
  trans
    (cong
      (λ prefix →
        prefix + eta * Sharp.inverseDyadicScale (suc lastShell))
      (requiredGainPrefixClosedForm eta lastShell))
    (ℚRing.solve-∀
      eta (Sharp.inverseDyadicScale (suc lastShell)))

requiredGainPrefixIncrement :
  ∀ eta lastShell →
  requiredGainPrefix eta (suc lastShell)
    - requiredGainPrefix eta lastShell
  ≡ Sharp.requiredHHBadGain eta (suc lastShell)
requiredGainPrefixIncrement eta lastShell =
  ℚRing.solve-∀
    (requiredGainPrefix eta lastShell)
    (Sharp.requiredHHBadGain eta (suc lastShell))

requiredGainTailHalves :
  ∀ eta lastShell →
  eta * Sharp.inverseDyadicScale (suc (suc lastShell))
  ≡ Sharp.half
      * (eta * Sharp.inverseDyadicScale (suc lastShell))
requiredGainTailHalves eta lastShell =
  ℚRing.solve-∀ eta (Sharp.inverseDyadicScale (suc lastShell))

requiredGainPrefixSuccessorConservation :
  ∀ eta lastShell →
  requiredGainPrefix eta (suc lastShell)
    + eta * Sharp.inverseDyadicScale (suc (suc lastShell))
  ≡ requiredGainPrefix eta lastShell
    + eta * Sharp.inverseDyadicScale (suc lastShell)
requiredGainPrefixSuccessorConservation eta lastShell =
  trans
    (requiredGainPrefixPlusTail eta (suc lastShell))
    (sym (requiredGainPrefixPlusTail eta lastShell))

record ExactSummableHHBadGainProfile (eta : ℚ) : Set where
  constructor exact-summable-hhbad-gain-profile
  field
    shellGain : Nat → ℚ
    shellGainExact : ∀ shell →
      shellGain shell ≡ Sharp.requiredHHBadGain eta shell

open ExactSummableHHBadGainProfile public

canonicalSummableHHBadGainProfile :
  ∀ eta → ExactSummableHHBadGainProfile eta
canonicalSummableHHBadGainProfile eta =
  exact-summable-hhbad-gain-profile
    (Sharp.requiredHHBadGain eta)
    (λ shell → refl)

profilePrefix :
  ∀ {eta} →
  ExactSummableHHBadGainProfile eta →
  Nat → ℚ
profilePrefix profile zero = shellGain profile zero
profilePrefix profile (suc lastShell) =
  profilePrefix profile lastShell + shellGain profile (suc lastShell)

profilePrefixAgreesCanonical :
  ∀ {eta}
    (profile : ExactSummableHHBadGainProfile eta)
    lastShell →
  profilePrefix profile lastShell ≡ requiredGainPrefix eta lastShell
profilePrefixAgreesCanonical profile zero =
  shellGainExact profile zero
profilePrefixAgreesCanonical profile (suc lastShell) =
  trans
    (cong
      (λ prefix → prefix + shellGain profile (suc lastShell))
      (profilePrefixAgreesCanonical profile lastShell))
    (cong
      (requiredGainPrefix _ lastShell +_)
      (shellGainExact profile (suc lastShell)))

profilePrefixPlusTailExact :
  ∀ {eta}
    (profile : ExactSummableHHBadGainProfile eta)
    lastShell →
  profilePrefix profile lastShell
    + eta * Sharp.inverseDyadicScale (suc lastShell)
  ≡ eta
profilePrefixPlusTailExact {eta} profile lastShell =
  trans
    (cong
      (λ prefix →
        prefix + eta * Sharp.inverseDyadicScale (suc lastShell))
      (profilePrefixAgreesCanonical profile lastShell))
    (requiredGainPrefixPlusTail eta lastShell)

hhBadDyadicTargetProfileSummableClosed : Bool
hhBadDyadicTargetProfileSummableClosed = true

physicalHHBadGainProfileProduced : Bool
physicalHHBadGainProfileProduced = false

hhBadDyadicTargetProfileSummableClosedIsTrue :
  hhBadDyadicTargetProfileSummableClosed ≡ true
hhBadDyadicTargetProfileSummableClosedIsTrue = refl

physicalHHBadGainProfileProducedIsFalse :
  physicalHHBadGainProfileProduced ≡ false
physicalHHBadGainProfileProducedIsFalse = refl
