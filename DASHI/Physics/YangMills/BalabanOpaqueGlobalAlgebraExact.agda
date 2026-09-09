module DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact where

------------------------------------------------------------------------
-- OPAQUE GLOBAL ALGEBRA LEAF
--
-- This module is intentionally forbidden from importing physical lattice,
-- martingale, Fourier, block, or field constructors.  Solver work happens only
-- on abstract rational coordinates.  Deep YM modules instantiate these lemmas
-- after their fibre/observer layers have already produced scalar equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

sixTermSumZero :
  ∀ {a b c d e f : ℚ} →
  a ≡ 0ℚ → b ≡ 0ℚ → c ≡ 0ℚ →
  d ≡ 0ℚ → e ≡ 0ℚ → f ≡ 0ℚ →
  a + (b + (c + (d + (e + f)))) ≡ 0ℚ
sixTermSumZero {a} {b} {c} {d} {e} {f}
  a0 b0 c0 d0 e0 f0
  rewrite a0 | b0 | c0 | d0 | e0 | f0 =
  solve-∀

dropScaledZero :
  ∀ (x scale : ℚ) →
  x + scale * 0ℚ ≡ x
dropScaledZero x scale = solve-∀
