module DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact where

------------------------------------------------------------------------
-- K04d P0.01: ORIGINAL LOG QUOTIENT HAS EXACT SECOND-ORDER FACTOR
--
-- Reuses original sourceLogFinitePartialFactorDerivative and
-- original finite polynomial powerDifferenceQuotient.
--
-- For every n, x, h:
--    Q_n(x,h) ~= Q_n(x,0) + h * T_n(x,h)
-- with T_0=0, T_(n+1)=T_n*(x+h)+Q_n(x,0).
--
-- Therefore the ORIGINAL finite-log factor quotient has
--    q_L,N(x,h) ~= q_L,N(x,0) + h * S_N(x,h)
-- with S_N a finite sum of genuine native reciprocal-weighted
-- T_(k+1). No division by h and no derivative-limit assumptions.
--
-- This is the algebraic factorisation consumed by a subsequent
-- order/compact-uniform modulus. It is not such a modulus itself.
--
-- Attribution: Bishop/Bridges, pinned Murray/Csimma Bishop Real,
-- DASHI power first-order, original log factor derivative owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExplicitQuotientExact as Explicit
import DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact as LogFinite

-- The next coefficient of the quotient defect is a source-native
-- finite polynomial, even when h=0.
sourcePowerSecondQuotient :
  (x h : R.ℝ) → Nat → R.ℝ
sourcePowerSecondQuotient x h zero = R.0ℝ
sourcePowerSecondQuotient x h (suc n) =
  R._+_
    (R._*_
      (sourcePowerSecondQuotient x h n)
      (R._+_ x h))
    (Power.powerDifferenceQuotient x R.0ℝ n)

originalPowerQuotientSecondOrder :
  (x h : R.ℝ) (n : Nat) →
  R._≃_
    (Power.powerDifferenceQuotient x h n)
    (R._+_
      (Power.powerDifferenceQuotient x R.0ℝ n)
      (R._*_ h (sourcePowerSecondQuotient x h n)))
originalPowerQuotientSecondOrder x h zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ hh →
      Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ (hh ⊗ Κ 0ℚᵘ))
    RP.≃-refl h
originalPowerQuotientSecondOrder x h (suc n) =
  let
    q0 = Power.powerDifferenceQuotient x R.0ℝ n
    t = sourcePowerSecondQuotient x h n
    p = R.pow x n
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (RP.*-cong
        (originalPowerQuotientSecondOrder x h n)
        RP.≃-refl)
      RP.≃-refl)
    (solve 5
      (λ xx hh qzero tt pp →
        ((qzero ⊕ (hh ⊗ tt)) ⊗ (xx ⊕ hh)) ⊕ pp
        ⊜ ((qzero ⊗ (xx ⊕ Κ 0ℚᵘ)) ⊕ pp)
          ⊕ (hh ⊗ ((tt ⊗ (xx ⊕ hh)) ⊕ qzero)))
      RP.≃-refl x h q0 t p)

-- Genuine original finite-log coefficients, not arbitrary
-- selected weights.
sourceFiniteLogSecondQuotient :
  (x h : R.ℝ) → Nat → R.ℝ
sourceFiniteLogSecondQuotient x h zero = R.0ℝ
sourceFiniteLogSecondQuotient x h (suc n) =
  R._+_
    (sourceFiniteLogSecondQuotient x h n)
    (R._*_
      (LogFinite.sourceLogCoefficient n)
      (sourcePowerSecondQuotient x h (suc n)))

-- This is a finite exact identity for the actual source log factor
-- quotient. A boundedness theorem for S_N is needed before
-- one may deduce a compact-uniform |q_L(N,x,h)-L'_N(x)| modulus.
originalFiniteLogQuotientSecondOrder :
  (x h : R.ℝ) (n : Nat) →
  R._≃_
    (Explicit.originalSourceFiniteLogQuotient n x h)
    (R._+_
      (Explicit.originalSourceFiniteLogQuotient n x R.0ℝ)
      (R._*_ h (sourceFiniteLogSecondQuotient x h n)))
originalFiniteLogQuotientSecondOrder x h zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ hh → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ (hh ⊗ Κ 0ℚᵘ))
    RP.≃-refl h
originalFiniteLogQuotientSecondOrder x h (suc n) =
  let
    q0 = Explicit.originalSourceFiniteLogQuotient n x R.0ℝ
    t = sourceFiniteLogSecondQuotient x h n
    coeff = LogFinite.sourceLogCoefficient n
    p0 = Power.powerDifferenceQuotient x R.0ℝ (suc n)
    ps = sourcePowerSecondQuotient x h (suc n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (originalFiniteLogQuotientSecondOrder x h n)
      (RP.*-cong
        RP.≃-refl
        (originalPowerQuotientSecondOrder x h (suc n))))
    (solve 6
      (λ old hh tail cc pp ss →
        (old ⊕ (hh ⊗ tail))
          ⊕ (cc ⊗ (pp ⊕ (hh ⊗ ss)))
        ⊜ (old ⊕ (cc ⊗ pp))
          ⊕ (hh ⊗ (tail ⊕ (cc ⊗ ss))))
      RP.≃-refl q0 h t coeff p0 ps)
