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
-- then the cutoff-shifted path (q,n)=(m+1,m) is bounded by
--
--   (3/2) 2^{-m},
--
-- while the next diagonal point (m+1,m+1) is bounded by 2^{-m}.  These are
-- computable joint cutoff/terminal-time moduli of the kind required before
-- either limiting operation is promoted.
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

half threeHalves : ℚ
half = Int.+ 1 / 2
threeHalves = Int.+ 3 / 2

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

cutoffShiftedModulus :
  (modulus : GeometricCutoffTimeModulus) →
  (index : Nat) →
  error modulus (suc index) index
  ≤ threeHalves * Geo.pow half index
cutoffShiftedModulus modulus index =
  subst
    (λ upper → error modulus (suc index) index ≤ upper)
    (solve (Geo.pow half index ∷ []))
    (errorBound modulus (suc index) index)

nextDiagonalModulus :
  (modulus : GeometricCutoffTimeModulus) →
  (index : Nat) →
  error modulus (suc index) (suc index)
  ≤ Geo.pow half index
nextDiagonalModulus modulus index =
  subst
    (λ upper → error modulus (suc index) (suc index) ≤ upper)
    (solve (Geo.pow half index ∷ []))
    (diagonalBound modulus (suc index))
