module DASHI.Analysis.BishopOriginalNegativeLogFiniteExplicitQuotientExact where

------------------------------------------------------------------------
-- P0: EXPOSE THE ORIGINAL COMPOSITE FINITE LOG-EXP QUOTIENT.
--
-- The prior exact mesh/derivative result used Factor.quotient D
-- abstractly. The original derivative is not an arbitrary quotient:
--
-- q_F,N(x,h) =
--   [ -1 * q_L,N(x,h) ] *
--   [ exp_B(-L_N(x)) * Q(-(L_N(x+h)-L_N(x))) ],
--
-- where q_L,N is the division-free source finite-log factor
-- quotient and Q(t)=Σ t^k/(k+1)! is the actual original shifted
-- factorial-series limit, already proven convergent.
--
-- These are the EXACT functions constructed by existing source
-- chain, congruence and exponential-Cauchy-product receipts.
-- This changes the next analytic cut from an opaque factor-quotient
-- modulus to explicit bounds on one finite log polynomial quotient
-- and the actual shifted factorial series Q.
--
-- Pure definitional unfolding, without a new derivative operator,
-- synthetic exponential or postulated uniform modulus.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRecip
import DASHI.Analysis.BishopFactorDerivativeChainExact as Chain
import DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact as LogFinite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpDerivativeResidualExact as Residual
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalExpOriginDividedDifferenceSeriesExact as Origin
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp

originalSourceFiniteLogQuotient :
  (n : Nat) (x h : R.ℝ) → R.ℝ
originalSourceFiniteLogQuotient n x h =
  Factor.quotient
    (LogFinite.originalLogFinitePartialFactorDerivative x n)
    h

originalSourceNegativeLogIncrement :
  (n : Nat) (x h : R.ℝ) → R.ℝ
originalSourceNegativeLogIncrement n x h =
  Chain.factorChainDelta
    (λ y → R.-_ (LogFinite.originalLogFinitePartial y n))
    x h

originalSourceFiniteLogExpExplicitQuotient :
  (n : Nat) (x h : R.ℝ) → R.ℝ
originalSourceFiniteLogExpExplicitQuotient n x h =
  R._*_
    (R._*_ (R.-_ R.1ℝ)
      (originalSourceFiniteLogQuotient n x h))
    (R._*_
      (Exp.bishopExp
        (R.-_ (LogFinite.originalLogFinitePartial x n)))
      (Origin.originalExpOriginQuotient
        (originalSourceNegativeLogIncrement n x h)))

-- Source-level definitional computation: unfold the original
-- Chain.factorDerivativeChain quotient, the original
-- Global.originalBishopExpGlobalFactorDerivativeFromOrigin
-- quotient, and the original scaled finite LOG quotient.
originalFiniteLogExpQuotientIsExplicit :
  (n : Nat) (x h : R.ℝ) →
  R._≃_
    (Factor.quotient
      (Residual.originalFiniteNegativeLogExpDerivative x n)
      h)
    (originalSourceFiniteLogExpExplicitQuotient n x h)
originalFiniteLogExpQuotientIsExplicit n x h =
  RP.≃-refl

-- This is the exact expression that the endpoint-mesh P0 bound
-- has to control: no hidden modulus inside a free Set-valued field.
originalFiniteLogErrorQuotientIsExplicit :
  (n : Nat) (x h : R.ℝ) →
  R._≃_
    (Factor.quotient
      (Error.originalFiniteLogExpErrorDerivative n x)
      h)
    (R._+_
      (originalSourceFiniteLogExpExplicitQuotient n x h)
      R.1ℝ)
originalFiniteLogErrorQuotientIsExplicit n x h =
  RP.+-cong
    (originalFiniteLogExpQuotientIsExplicit n x h)
    RP.≃-refl

-- No source-log quotient is left as an opaque record selector:
-- the finite source polynomial quotient is a literal sum of the
-- already-verified power difference quotients.
originalSourceFiniteLogQuotientZero :
  (x h : R.ℝ) →
  R._≃_ (originalSourceFiniteLogQuotient 0 x h) R.0ℝ
originalSourceFiniteLogQuotientZero x h =
  RP.≃-refl

originalSourceFiniteLogQuotientSuccessor :
  (n : Nat) (x h : R.ℝ) →
  R._≃_
    (originalSourceFiniteLogQuotient (suc n) x h)
    (R._+_
      (originalSourceFiniteLogQuotient n x h)
      (R._*_
        (R._⋆ (NatRecip.reciprocalNatRational n))
        (Power.powerDifferenceQuotient x h (suc n))))
originalSourceFiniteLogQuotientSuccessor n x h =
  RP.≃-refl
