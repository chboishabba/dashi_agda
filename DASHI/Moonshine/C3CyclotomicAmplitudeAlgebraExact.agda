module DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Lawrence C. Washington,
-- "Introduction to Cyclotomic Fields", Second Edition,
-- Springer Graduate Texts in Mathematics 83, 1997.
-- DOI: 10.1007/978-1-4612-1934-7.
--
-- DASHI CONTRIBUTION
--
-- Replace the finite slogan "phase -> real invariant" by the exact amplitude
-- algebra Q(zeta_3).  In the basis (1,zeta), using zeta^2 + zeta + 1 = 0,
-- write x = u + v zeta.  Then
--
--   conjugate(x) = (u-v) - v zeta,
--   Tr(x)         = 2u - v,
--   N(x)          = u^2 - uv + v^2.
--
-- Multiplication and conjugation are implemented directly over exact rational
-- coordinates, and x*conjugate(x) is proved to land on the rational axis with
-- scalar coordinate N(x).  The rational axis embeds as (r,0).
--
-- This is an algebraic real-descent layer.  It does not identify Q with R or
-- construct the analytic completion of Q; those are separate topological
-- obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record Cyclotomic3 : Set where
  constructor cyclotomic3
  field
    rationalCoeff : ℚ
    zetaCoeff : ℚ

open Cyclotomic3 public

cyclotomic3Ext : ∀ {left right} →
  rationalCoeff left ≡ rationalCoeff right →
  zetaCoeff left ≡ zetaCoeff right →
  left ≡ right
cyclotomic3Ext {cyclotomic3 _ _} {cyclotomic3 _ _} refl refl = refl

zero one zeta zetaSquared : Cyclotomic3
zero = cyclotomic3 0ℚ 0ℚ
one = cyclotomic3 1ℚ 0ℚ
zeta = cyclotomic3 0ℚ 1ℚ
zetaSquared = cyclotomic3 (- 1ℚ) (- 1ℚ)

embedRational : ℚ → Cyclotomic3
embedRational r = cyclotomic3 r 0ℚ

conjugate : Cyclotomic3 → Cyclotomic3
conjugate (cyclotomic3 u v) = cyclotomic3 (u - v) (- v)

multiply : Cyclotomic3 → Cyclotomic3 → Cyclotomic3
multiply (cyclotomic3 u v) (cyclotomic3 x y) =
  cyclotomic3
    (u * x - v * y)
    (u * y + v * x - v * y)

trace : Cyclotomic3 → ℚ
trace (cyclotomic3 u v) = u + u - v

norm : Cyclotomic3 → ℚ
norm (cyclotomic3 u v) = u * u - u * v + v * v

------------------------------------------------------------------------
-- Exact phase algebra.

zetaSquaredIsZetaTimesZeta : multiply zeta zeta ≡ zetaSquared
zetaSquaredIsZetaTimesZeta =
  cyclotomic3Ext refl refl

zetaCubedIsOne : multiply zetaSquared zeta ≡ one
zetaCubedIsOne = cyclotomic3Ext refl refl

conjugateZetaIsZetaSquared : conjugate zeta ≡ zetaSquared
conjugateZetaIsZetaSquared = cyclotomic3Ext refl refl

conjugateZetaSquaredIsZeta : conjugate zetaSquared ≡ zeta
conjugateZetaSquaredIsZeta = cyclotomic3Ext refl refl

zetaTimesConjugateZetaIsOne : multiply zeta (conjugate zeta) ≡ one
zetaTimesConjugateZetaIsOne = cyclotomic3Ext refl refl

------------------------------------------------------------------------
-- Conjugation and real-valued trace/norm descent.

conjugationInvolutive : (value : Cyclotomic3) →
  conjugate (conjugate value) ≡ value
conjugationInvolutive (cyclotomic3 u v) =
  cyclotomic3Ext step1 step2
  where
    step1 : (u - v) - (- v) ≡ u
    step1 = solve (u ∷ v ∷ [])

    step2 : - (- v) ≡ v
    step2 = solve (v ∷ [])

traceConjugationInvariant : (value : Cyclotomic3) →
  trace (conjugate value) ≡ trace value
traceConjugationInvariant (cyclotomic3 u v) = step
  where
    step : ((u - v) + (u - v)) - (- v) ≡ (u + u) - v
    step = solve (u ∷ v ∷ [])

normConjugationInvariant : (value : Cyclotomic3) →
  norm (conjugate value) ≡ norm value
normConjugationInvariant (cyclotomic3 u v) = step
  where
    step :
      ((u - v) * (u - v) - (u - v) * (- v)) + (- v) * (- v)
      ≡ (u * u - u * v) + v * v
    step = solve (u ∷ v ∷ [])

multiplyByConjugateLandsOnNorm : (value : Cyclotomic3) →
  multiply value (conjugate value) ≡ embedRational (norm value)
multiplyByConjugateLandsOnNorm (cyclotomic3 u v) =
  cyclotomic3Ext step1 step2
  where
    step1 : (u * (u - v)) - (v * (- v)) ≡ ((u * u) - (u * v)) + (v * v)
    step1 = solve (u ∷ v ∷ [])

    step2 : ((u * (- v)) + (v * (u - v))) - (v * (- v)) ≡ 0ℚ
    step2 = solve (u ∷ v ∷ [])

------------------------------------------------------------------------
-- Calibration on the three C3 phases.

traceOneIsTwo : trace one ≡ 1ℚ + 1ℚ
traceOneIsTwo = refl

traceZetaIsMinusOne : trace zeta ≡ - 1ℚ
traceZetaIsMinusOne = refl

traceZetaSquaredIsMinusOne : trace zetaSquared ≡ - 1ℚ
traceZetaSquaredIsMinusOne = refl

normOneIsOne : norm one ≡ 1ℚ
normOneIsOne = refl

normZetaIsOne : norm zeta ≡ 1ℚ
normZetaIsOne = refl

normZetaSquaredIsOne : norm zetaSquared ≡ 1ℚ
normZetaSquaredIsOne = refl

------------------------------------------------------------------------
-- Rational-axis calibration.  This is the fixed-field direction used by the
-- later analytic completion, but no completeness theorem is asserted here.

conjugateEmbeddedRational : (r : ℚ) →
  conjugate (embedRational r) ≡ embedRational r
conjugateEmbeddedRational r =
  cyclotomic3Ext step1 step2
  where
    step1 : r - 0ℚ ≡ r
    step1 = solve (r ∷ [])

    step2 : - 0ℚ ≡ 0ℚ
    step2 = refl

traceEmbeddedRational : (r : ℚ) →
  trace (embedRational r) ≡ r + r
traceEmbeddedRational r = step
  where
    step : (r + r) - 0ℚ ≡ r + r
    step = solve (r ∷ [])

normEmbeddedRational : (r : ℚ) →
  norm (embedRational r) ≡ r * r
normEmbeddedRational r = step
  where
    step : ((r * r) - (r * 0ℚ)) + (0ℚ * 0ℚ) ≡ r * r
    step = solve (r ∷ [])
