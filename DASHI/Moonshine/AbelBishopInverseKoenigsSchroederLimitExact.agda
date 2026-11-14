module DASHI.Moonshine.AbelBishopInverseKoenigsSchroederLimitExact where

------------------------------------------------------------------------
-- EXACT INVERSE-KOENIGS SCHROEDER LIMIT TRANSPORT.
--
-- On the original Bishop complex carrier, with the finite orbit
--
--  h_n(z) = p^n *C (g^n(z) -C p),
--
-- the previous source proof establishes
--
--  p *C h_n(g(z)) ≈C h_(n+1)(z).
--
-- Using actual Bishop product continuity, successor subsequence
-- convergence and uniqueness of limits, the present theorem proves
--
--  p *C Ψ(g(z)) ≈C Ψ(z)
--
-- whenever the TWO ACTUAL source trajectories h_n(z), h_n(g(z))
-- have already been proved to converge to Ψ(z), Ψ(g(z)).
--
-- This is a fail-closed analytic consumer, NOT a supplied
-- inverse-logarithm contraction, fixed-point or convergence proof.
-- In particular p is not silently replaced by its numeric estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Multiply
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit
import DASHI.Moonshine.AbelBishopInverseKoenigsShiftConvergenceExact as Shift

originalBishopInverseKoenigsLimitSchroeder :
  (p : Complex.BishopComplex) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  (z ψz ψgz : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Orbit.inverseKoenigsPrefix p g n z)
    ψz →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Orbit.inverseKoenigsPrefix p g n (g z))
    ψgz →
  Complex._≈C_
    (Algebra._*C_ p ψgz)
    ψz
originalBishopInverseKoenigsLimitSchroeder
  p g z ψz ψgz convergesZ convergesGZ =
  let
    multipliedConverges =
      Multiply.originalBishopConstantComplexMultiplyConverges
        p
        (λ n → Orbit.inverseKoenigsPrefix p g n (g z))
        ψgz
        convergesGZ

    successorConverges =
      Shift.originalBishopInverseKoenigsSuccessorConverges
        p g z ψz convergesZ

    realShiftConvergesToMultiplied =
      BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ n → proj₁ (Orbit.inverseKoenigsPrefixStep p g n z))
        (Complex.re (Algebra._*C_ p ψgz) ,
          Completion.realConverges multipliedConverges)

    imaginaryShiftConvergesToMultiplied =
      BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ n → proj₂ (Orbit.inverseKoenigsPrefixStep p g n z))
        (Complex.im (Algebra._*C_ p ψgz) ,
          Completion.imaginaryConverges multipliedConverges)

    realEquality :
      BishopReal._≃_
        (Complex.re (Algebra._*C_ p ψgz))
        (Complex.re ψz)
    realEquality =
      BishopSequence.uniqueness-of-limits
        (Complex.re (Algebra._*C_ p ψgz) ,
          realShiftConvergesToMultiplied)
        (Complex.re ψz ,
          Completion.realConverges successorConverges)

    imaginaryEquality :
      BishopReal._≃_
        (Complex.im (Algebra._*C_ p ψgz))
        (Complex.im ψz)
    imaginaryEquality =
      BishopSequence.uniqueness-of-limits
        (Complex.im (Algebra._*C_ p ψgz) ,
          imaginaryShiftConvergesToMultiplied)
        (Complex.im ψz ,
          Completion.imaginaryConverges successorConverges)
  in
  realEquality , imaginaryEquality
