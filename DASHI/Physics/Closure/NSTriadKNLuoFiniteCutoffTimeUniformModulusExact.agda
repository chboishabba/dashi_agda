module DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffTimeUniformModulusExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Mathematical ingredient: effective uniform convergence with an explicit
-- separable modulus.
-- Title: "Finite cutoff-time geometric uniformity modulus".
-- Author: DASHI repository contributors.
-- DOI: not applicable; this is a repository-original finite theorem.
--
-- PURPOSE
-- State and prove the exact positive counterpart of the diagonal no-go.  If a
-- two-parameter physical error is dominated by
--
--   2^{-q} + 2^{-n},
--
-- then on the shifted diagonal q=n+1 it obeys the computable bound 2^{-n}.
-- This is the form of joint cutoff/terminal-time modulus that must be supplied
-- by the continuum estimates before either limiting operation is promoted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; _/_; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

half : ℚ
half = Int.+ 1 / 2

record GeometricCutoffTimeModulus : Set₁ where
  field
    error : Nat → Nat → ℚ
    errorBound :
      (cutoff terminalIndex : Nat) →
      error cutoff terminalIndex
      ≤ Geo.pow half cutoff + Geo.pow half terminalIndex

open GeometricCutoffTimeModulus public

diagonalBound :
  (modulus : GeometricCutoffTimeModulus) →
  (index : Nat) →
  error modulus index index
  ≤ (Int.+ 2 / 1) * Geo.pow half index
diagonalBound modulus index =
  subst
    (λ upper → error modulus index index ≤ upper)
    (solve (Geo.pow half index ∷ []))
    (errorBound modulus index index)

shiftedDiagonalModulus :
  (modulus : GeometricCutoffTimeModulus) →
  (index : Nat) →
  error modulus (suc index) (suc index)
  ≤ Geo.pow half index
shiftedDiagonalModulus modulus index =
  subst
    (λ upper → error modulus (suc index) (suc index) ≤ upper)
    (solve (Geo.pow half index ∷ []))
    (diagonalBound modulus (suc index))
