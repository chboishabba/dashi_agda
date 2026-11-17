module DASHI.Analysis.BishopOriginalNegativeLogFiniteExpInitialValueExact where

------------------------------------------------------------------------
-- P0: literal finite LOG/EXP initial value on the pinned Bishop real.
--
-- For each natural finite stage N, including N=0:
--
--  L_N(0) ~= 0
--  F_N(0) = exp_B(-L_N(0)) ~= 1.
--
-- This pays the actual endpoint datum needed by an FTC/stability
-- argument. It does not assert an FTC or deduce the original LOG
-- terminal identity without an integrated residual estimate.
--
-- Reuse original source terms and original exponential; no formal
-- coefficient surrogate or abstract initial-value authority.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRecip
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite

originalNegativeLogTermAtZero :
  (n : Nat) →
  R._≃_ (Log.sourceNegativeLogTerm R.0ℝ n) R.0ℝ
originalNegativeLogTermAtZero n =
  let open RP.ℝ-Solver in
  solve 2
    (λ previous reciprocal →
      ((previous ⊗ Κ 0ℚᵘ) ⊗ reciprocal) ⊜ Κ 0ℚᵘ)
    RP.≃-refl
    (R.pow R.0ℝ n)
    (R._⋆
      (NatRecip.reciprocalNatRational n))

originalNegativeLogFiniteAtZero :
  (n : Nat) →
  R._≃_ (Finite.originalLogFinitePartial R.0ℝ n) R.0ℝ
originalNegativeLogFiniteAtZero zero = RP.≃-refl
originalNegativeLogFiniteAtZero (suc n) =
  RP.≃-trans
    (RP.+-cong
      (originalNegativeLogFiniteAtZero n)
      (originalNegativeLogTermAtZero n))
    (let open RP.ℝ-Solver in
     solve 0 (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       RP.≃-refl)

originalFiniteNegativeLogExpAtZero :
  (n : Nat) →
  R._≃_
    (Finite.originalNegativeLogFiniteExponential R.0ℝ n)
    R.1ℝ
originalFiniteNegativeLogExpAtZero n =
  RP.≃-trans
    (ExpCong.bishopExpCongruent
      (RP.≃-trans
        (RP.-‿cong (originalNegativeLogFiniteAtZero n))
        (let open RP.ℝ-Solver in
         solve 0 (⊝ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
           RP.≃-refl)))
    ExpZero.bishopExpZero
