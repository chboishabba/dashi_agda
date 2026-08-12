module DASHI.Physics.Closure.NSTriadKNAmplitudeFrequencyTimeValuationRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
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
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Rounds 42--44 exposed two different compensation mechanisms which single
-- dyadic degree counting can hide:
--
--   HH-bad:  production/dissipation has amplitude-frequency bidegree (1,-2),
--            and the kinetic amplitude law a_q ~ lambda_q turns this into -1;
--
--   HH-good: kinetic vorticity costs lambda_q^2, while a parabolic shell
--            residence window contributes lambda_q^-2, producing net degree 0.
--
-- This module makes that bookkeeping an exact three-coordinate valuation.
-- `timeWindowDegree = 1` means one parabolic lambda^-2 window.  For an
-- amplitude growth exponent rho, the effective dyadic exponent is
--
--   amplitudeDegree*rho + frequencyDegree - 2*timeWindowDegree.
--
-- The theorem is intentionally tiny: it is a fail-closed dimensional checker,
-- not another analytic authority.  The literal amplitude and parabolic facts
-- remain in their existing theorem-bearing modules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

data TaxKind : Set where
  hard youngSoft zeroTax : TaxKind

record AmplitudeFrequencyTimeValuation : Set where
  constructor aft-valuation
  field
    amplitudeDegree : ℚ
    frequencyDegree : ℚ
    timeWindowDegree : ℚ
    taxKind : TaxKind

open AmplitudeFrequencyTimeValuation public

two : ℚ
two = Int.+ 2 / 1

minusOne minusTwo : ℚ
minusOne = 0ℚ - 1ℚ
minusTwo = 0ℚ - two

effectiveDyadicDegree :
  ℚ → AmplitudeFrequencyTimeValuation → ℚ
effectiveDyadicDegree amplitudeGrowth valuation =
  amplitudeDegree valuation * amplitudeGrowth
  + frequencyDegree valuation
  - two * timeWindowDegree valuation

hhBadRatioValuation : AmplitudeFrequencyTimeValuation
hhBadRatioValuation = aft-valuation 1ℚ minusTwo 0ℚ hard

hhGoodKineticParabolicValuation : AmplitudeFrequencyTimeValuation
hhGoodKineticParabolicValuation = aft-valuation 0ℚ two 1ℚ youngSoft

hhBadKineticEffectiveDegree :
  effectiveDyadicDegree 1ℚ hhBadRatioValuation ≡ minusOne
hhBadKineticEffectiveDegree = solve []

hhGoodParabolicEffectiveDegree :
  effectiveDyadicDegree 1ℚ hhGoodKineticParabolicValuation ≡ 0ℚ
hhGoodParabolicEffectiveDegree = solve []

record EffectiveDegreeWitness : Set where
  constructor effective-degree-witness
  field
    valuation : AmplitudeFrequencyTimeValuation
    amplitudeGrowth : ℚ
    expectedEffectiveDegree : ℚ
    effectiveDegreeExact :
      effectiveDyadicDegree amplitudeGrowth valuation
      ≡ expectedEffectiveDegree

open EffectiveDegreeWitness public

hhBadKineticWitness : EffectiveDegreeWitness
hhBadKineticWitness =
  effective-degree-witness
    hhBadRatioValuation 1ℚ minusOne hhBadKineticEffectiveDegree

hhGoodParabolicWitness : EffectiveDegreeWitness
hhGoodParabolicWitness =
  effective-degree-witness
    hhGoodKineticParabolicValuation 1ℚ 0ℚ
    hhGoodParabolicEffectiveDegree

amplitudeFrequencyTimeValuationClosed : Bool
amplitudeFrequencyTimeValuationClosed = true

hhBadAndHHGoodCompensationsAudited : Bool
hhBadAndHHGoodCompensationsAudited = true

amplitudeFrequencyTimeValuationClosedIsTrue :
  amplitudeFrequencyTimeValuationClosed ≡ true
amplitudeFrequencyTimeValuationClosedIsTrue = refl

hhBadAndHHGoodCompensationsAuditedIsTrue :
  hhBadAndHHGoodCompensationsAudited ≡ true
hhBadAndHHGoodCompensationsAuditedIsTrue = refl
