module DASHI.Physics.YangMills.YMClayCMP102OriginalGPrefixSignedSquaresBIDIExact where

------------------------------------------------------------------------
-- CMP102 original represented finite G-prefix signed-square weld.
-- This is finite Bishop-real algebra on the ORIGINAL source values.
-- No alternate coefficients, limit, Taylor carrier or assertion G=0.
-- Source-written: requires native Agda typecheck.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

-- Use the same source values, with their actual Sequence.SeriesOf count
-- semantics: sums from index 0 through count - 1.
originalSignedSquares : R.ℝ → Nat → R.ℝ
originalSignedSquares X count =
  let
    A = Original.aPrefix X count
    B = Original.bPrefix X count
  in
  R._+_
    (R._-_
      (R._*_ (R._-_ R.1ℝ A) (R._-_ R.1ℝ A))
      (R._*_ (R._+_ R.1ℝ X) (R._*_ A A)))
    (R._*_
      (R._*_ X B)
      (R._+_ Original.CMP102.two (R._*_ X B)))

-- All degrees, all X and all finite count. The leading coefficient
-- cancels only AFTER the source's original even/odd Cauchy parity:
-- this purely algebraic rewrite is not a zero theorem.
originalGPrefixSignedSquares :
  ∀ X count →
  R._≃_ (Original.originalGPrefix X count)
        (originalSignedSquares X count)
originalGPrefixSignedSquares X count =
  let
    A = Original.aPrefix X count
    B = Original.bPrefix X count
    open P.ℝ-Solver
  in
  solve 3
    (λ x a b →
      (((Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ a))
        ⊖ (x ⊗ (a ⊗ a)))
        ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ b)
        ⊕ ((x ⊗ x) ⊗ (b ⊗ b))
        ⊜
        (((Κ 1ℚᵘ ⊖ a) ⊗ (Κ 1ℚᵘ ⊖ a))
        ⊖ ((Κ 1ℚᵘ ⊕ x) ⊗ (a ⊗ a)))
        ⊕ ((x ⊗ b) ⊗ (Κ (+ 2 / 1) ⊕ (x ⊗ b)))))
    P.≃-refl X A B
