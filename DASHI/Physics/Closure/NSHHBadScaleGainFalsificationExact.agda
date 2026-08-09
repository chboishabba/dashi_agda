module DASHI.Physics.Closure.NSHHBadScaleGainFalsificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin,
-- "Fourier Analysis and Nonlinear Partial Differential Equations",
-- Grundlehren der mathematischen Wissenschaften 343, Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Xiaoyutao Luo,
-- "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization", Journal of Mathematical Fluid Mechanics 21 (2019), 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Falsify the raw HH-bad Bernstein lane and quantify the exact missing gain.
-- A half-kernel time factor times a two-derivative curvature cost leaves
--
--   rawHHBadCost(q) = 2 * 2^q,
--
-- which doubles with q.  To absorb the term with viscosity coefficient eta,
-- the physical mechanism must supply at least
--
--   requiredHHBadGain(eta,q) = (eta/2) * 2^-q.
--
-- The calibration theorem proves that this gain cancels the entire scale
-- loss exactly.  Any proposed physicalHHBadEstimate must therefore identify
-- a concrete source of this decay (alignment, short-time support,
-- dissipation-range localization, intermittency or another signed
-- cancellation); raw Bernstein alone cannot be cutoff-uniform.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

half two oneSixtyFourth : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1
oneSixtyFourth = Int.+ 1 / 64

dyadicScale : Nat → ℚ
dyadicScale zero = 1ℚ
dyadicScale (suc shell) = two * dyadicScale shell

inverseDyadicScale : Nat → ℚ
inverseDyadicScale zero = 1ℚ
inverseDyadicScale (suc shell) = half * inverseDyadicScale shell

dyadicScaleSuccessor :
  ∀ shell → dyadicScale (suc shell) ≡ two * dyadicScale shell
dyadicScaleSuccessor shell = refl

inverseDyadicReciprocal :
  ∀ shell → inverseDyadicScale shell * dyadicScale shell ≡ 1ℚ
inverseDyadicReciprocal zero = refl
inverseDyadicReciprocal (suc shell)
  rewrite inverseDyadicReciprocal shell =
  ℚRing.solve []

rawHHBadCost : Nat → ℚ
rawHHBadCost shell = two * dyadicScale shell

rawHHBadCostDoubles :
  ∀ shell → rawHHBadCost (suc shell) ≡ two * rawHHBadCost shell
rawHHBadCostDoubles shell =
  trans
    (cong (two *_) (dyadicScaleSuccessor shell))
    (ℚRing.solve-∀ (dyadicScale shell))

rawHHBadAlreadyExceedsOneSixtyFourth :
  oneSixtyFourth ≤ rawHHBadCost zero
rawHHBadAlreadyExceedsOneSixtyFourth =
  toWitness {a? = oneSixtyFourth ≤? rawHHBadCost zero} _

requiredHHBadGain : ℚ → Nat → ℚ
requiredHHBadGain eta shell =
  eta * half * inverseDyadicScale shell

requiredHHBadGainCalibration :
  ∀ eta shell →
  requiredHHBadGain eta shell * rawHHBadCost shell ≡ eta
requiredHHBadGainCalibration eta shell =
  trans
    (ℚRing.solve-∀ eta (inverseDyadicScale shell) (dyadicScale shell))
    (trans
      (cong (eta *_) (inverseDyadicReciprocal shell))
      (ℚRing.solve-∀ eta))

physicalHHBadEstimateFromScaleGain :
  ∀ eta shell badTerm dissipation →
  badTerm
  ≤ requiredHHBadGain eta shell * rawHHBadCost shell * dissipation →
  badTerm ≤ eta * dissipation
physicalHHBadEstimateFromScaleGain eta shell badTerm dissipation bounded =
  subst
    (λ upper → badTerm ≤ upper * dissipation)
    (requiredHHBadGainCalibration eta shell)
    bounded
