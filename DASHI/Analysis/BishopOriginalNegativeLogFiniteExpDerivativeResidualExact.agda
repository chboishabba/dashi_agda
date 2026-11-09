{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalNegativeLogFiniteExpDerivativeResidualExact where

------------------------------------------------------------------------
-- P0: the finite exponential of the ACTUAL negative-log partial sum
-- has a source-native factor derivative with a vanishing ODE residual.
--
-- F_N(x) = exp_B (-Σ_(k<N) x^(k+1)/(k+1))
-- P_N(x) = Σ_(k<N) x^k
--
--   F_N'(x) = F_N(x) * (-P_N(x))
--   (1-x) F_N'(x) + F_N(x) = F_N(x) * x^N.
--
-- The only algebraic input is the proved original geometric
-- telescope (1-x)P_N(x) = 1-x^N.  The first identity uses only the
-- original Bishop exp derivative and the source finite LOG
-- derivative, via the existing division-free chain rule.
--
-- This does not yet infer the terminal exp(-L_B)=1-x:
-- an analytic ODE/finite-residual uniqueness or integrated error
-- theorem is still required. No postulate, no arbitrary derivative
-- function, no synthetic log/exp definitions.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as Seq
import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopFactorDerivativeChainExact as Chain
import DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact as LogFinite
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalExpOriginDerivativeClosedExact as ExpDeriv
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log

-- The original negative sign, expressed on the SAME pinned Bishop
-- real carrier, agrees with the existing source `R.-_`.
originalNegIsMinusOneTimes :
  (y : R.ℝ) →
  R._≃_ (R.-_ y) (R._*_ (R.-_ R.1ℝ) y)
originalNegIsMinusOneTimes y =
  let open RP.ℝ-Solver in
  solve 1
    (λ value → ⊝ value ⊜ (⊝ Κ 1ℚᵘ) ⊗ value)
    RP.≃-refl y

originalFiniteNegativeLogDerivative :
  (x : R.ℝ) (n : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → R.-_ (LogFinite.originalLogFinitePartial y n))
    x
    (R.-_ (Geo.negativeLogDerivativePolynomial x n))
originalFiniteNegativeLogDerivative x n =
  Factor.factorDerivativeCongruence
    (λ y → originalNegIsMinusOneTimes
      (LogFinite.originalLogFinitePartial y n))
    (RP.≃-symm
      (originalNegIsMinusOneTimes
        (Geo.negativeLogDerivativePolynomial x n)))
    (Factor.factorDerivativeScale
      (R.-_ R.1ℝ)
      (LogFinite.originalLogFinitePartialFactorDerivative x n))

-- Native derivative of the ACTUAL finite-stage P0 exponential.
originalFiniteNegativeLogExpDerivative :
  (x : R.ℝ) (n : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → Finite.originalNegativeLogFiniteExponential y n)
    x
    (R._*_
      (Exp.bishopExp
        (R.-_ (LogFinite.originalLogFinitePartial x n)))
      (R.-_ (Geo.negativeLogDerivativePolynomial x n)))
originalFiniteNegativeLogExpDerivative x n =
  Chain.factorDerivativeChain
    ExpCong.bishopExpCongruent
    (ExpDeriv.originalBishopExponentialFactorDerivative
      (R.-_ (LogFinite.originalLogFinitePartial x n)))
    (originalFiniteNegativeLogDerivative x n)

-- The actual differential residual is the original x^N, not
-- an arbitrary majorant. This is a finite exact algebra theorem
-- holding for all Bishop real x and all finite N.
originalFiniteNegativeLogExpODEResidual :
  (x : R.ℝ) (n : Nat) →
  let
    f = Finite.originalNegativeLogFiniteExponential x n
    p = Geo.negativeLogDerivativePolynomial x n
  in
  R._≃_
    (R._+_
      (R._*_
        (R._-_ R.1ℝ x)
        (R._*_ f (R.-_ p)))
      f)
    (R._*_ f (R.pow x n))
originalFiniteNegativeLogExpODEResidual x n =
  let
    f = Finite.originalNegativeLogFiniteExponential x n
    p = Geo.negativeLogDerivativePolynomial x n
    z = R.pow x n
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 3
      (λ fx partial point →
        ((Κ 1ℚᵘ ⊖ point) ⊗ (fx ⊗ (⊝ partial))) ⊕ fx
        ⊜ fx ⊗ (Κ 1ℚᵘ ⊖
          ((Κ 1ℚᵘ ⊖ point) ⊗ partial)))
      RP.≃-refl f p x)
    (RP.*-cong
      RP.≃-refl
      (RP.≃-trans
        (RP.-‿cong
          (Geo.negativeLogDerivativeFiniteResidual x n))
        (solve 1
          (λ power → Κ 1ℚᵘ ⊖ (Κ 1ℚᵘ ⊖ power) ⊜ power)
          RP.≃-refl z)))

-- The EXACT residual of the finite original compositions tends to
-- ZERO pointwise in the original source limit, because the finite
-- composition is convergent and |x|<1 implies x^N -> 0. This is
-- stronger than mere coefficientwise vanishing of its formal jet.
originalFiniteNegativeLogExpODEResidualConvergesZero :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  (absInside : R._<_ (R.∣ x ∣) R.1ℝ) →
  Seq._ConvergesTo_
    (λ n →
      R._*_
        (Finite.originalNegativeLogFiniteExponential x n)
        (R.pow x n))
    R.0ℝ
originalFiniteNegativeLogExpODEResidualConvergesZero
    x positive belowOne absInside =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙyₙ→x₀y₀
      (Exp.bishopExp
        (R.-_ (Log.sourceNegativeLogValue x positive belowOne)) ,
        Finite.originalNegativeLogFiniteExponentialConverges
          x positive belowOne)
      (R.0ℝ , Seq.∣r∣<1⇒rⁿ→0 absInside))
    (let open RP.ℝ-Solver in
     solve 1
       (λ value → value ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       RP.≃-refl
       (Exp.bishopExp
         (R.-_ (Log.sourceNegativeLogValue x positive belowOne))))
