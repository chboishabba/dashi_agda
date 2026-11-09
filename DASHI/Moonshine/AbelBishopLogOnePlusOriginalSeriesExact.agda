module DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE LOCAL LOG(1+w) COEFFICIENTS, NOT A LOG AUTHORITY.
--
-- On the actual Bishop componentwise complex series carrier define
--   a_n(w) = (-1)^n * w^(n+1)/(n+1),  n >= 0.
--
-- The rational constructor has a nonzero positive denominator witness.
-- The present module supplies the literal terms, termwise setoid
-- congruence, and the existing Bishop canonical series-limit consumer.
--
-- OPEN: construct absolute convergence on |w|<1; show the limit is the
-- principal complex logarithm at 1+w; prove majorant inequalities.
-- None of those statements is an input field here.
--
-- Murray (2022), constructive Bishop real completion, vendored at the
-- repo's pinned bishop revision. Classical local logarithm series.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (ℚᵘ; _/_)

import Real as BishopReal
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra

alternate : Nat → Bool
alternate zero = false
alternate (suc n) with alternate n
... | false = true
... | true = false

alternateZero : alternate zero ≡ false
alternateZero = refl

alternateNext : ∀ n → alternate (suc (suc n)) ≡ alternate n
alternateNext zero = refl
alternateNext (suc n) with alternate n
... | false = refl
... | true = refl

inversePositiveNat : Nat → ℚᵘ
inversePositiveNat n = + 1 / suc n
  where
    instance
      denominatorNonzero : suc n ≢ zero
      denominatorNonzero ()

  -- Local definition avoids the off-by-one error from mkℚᵘ's raw
  -- denominator-minus-one representation.

logCoefficient : Nat → BishopReal.ℝ
logCoefficient n with alternate n
... | false = BishopReal._⋆ (inversePositiveNat n)
... | true = BishopReal.- (BishopReal._⋆ (inversePositiveNat n))

originalBishopLogOnePlusTerm :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopLogOnePlusTerm w n =
  Algebra.scaleC (logCoefficient n) (Algebra.powC w (suc n))

originalBishopLogOnePlusTermCongruent :
  ∀ {w w' : Complex.BishopComplex} →
  Complex._≈C_ w w' →
  ∀ n →
  Complex._≈C_
    (originalBishopLogOnePlusTerm w n)
    (originalBishopLogOnePlusTerm w' n)
originalBishopLogOnePlusTermCongruent equivalent n =
  Algebra.scaleCCongruent
    (Algebra.powCCongruent equivalent (suc n))
    (logCoefficient n)

-- Canonical Bishop componentwise limit is *derived* only after
-- the original terms' absolute convergence has actually been proved.
originalBishopLogOnePlusSeriesValue :
  (w : Complex.BishopComplex) →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (originalBishopLogOnePlusTerm w) →
  Complex.BishopComplex
originalBishopLogOnePlusSeriesValue w absolute =
  Complex.complexSeriesLimit
    (originalBishopLogOnePlusTerm w)
    absolute

originalBishopLogOnePlusSeriesConverges :
  (w : Complex.BishopComplex) →
  (absolute : Complex.ComponentwiseAbsoluteSeriesConvergent
    (originalBishopLogOnePlusTerm w)) →
  Complex.ComplexSeriesConvergesTo
    (originalBishopLogOnePlusTerm w)
    (originalBishopLogOnePlusSeriesValue w absolute)
originalBishopLogOnePlusSeriesConverges w absolute =
  Complex.complexSeriesLimitConvergence
    (originalBishopLogOnePlusTerm w)
    absolute
