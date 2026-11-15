module DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact where

------------------------------------------------------------------------
-- K04d/K05: IDENTIFY THE TWO EXISTING BISHOP COMPLEX PAIR CARRIERS.
--
-- Existing owners:
--   DASHI.Analysis.BishopSetoidComplexExact
--     - genuine Bishop Cartesian complex, original bishopExp, bishop
--       sine/cosine, expC and setoid congruence;
--   DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact
--     - exact Bishop Cartesian complex behind the original
--       RiemannAnalyticSubstrate.
--
-- They have different record constructors but IDENTICAL coordinate
-- carrier and arithmetic. We prove their literal inverse maps and
-- add/multiply/neg/conjugate compatibility by constructor reduction.
-- No carrier-equivalence authority, arbitrary bridge, or source fact
-- is postulated.
--
-- The exponential transported here is a genuine definition using
-- the original Bishop power-series exp/sin/cos, NOT a theorem that
-- it is already an AnalyticSubstrate.Function with the missing
-- half-plane zeta or original positive-Nat logarithm.
--
-- Sources: Bishop/Bridges 1985, Murray 2022 arXiv:2205.08354.
-- Proof ownership: original DASHI BishopSetoidComplexExact,
-- RiemannBishopComplexAnalyticCarrierExact, and new conversion.
-- Source-written Agda; golden Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)

import Real as R
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E

toAnalytic : C.BishopComplex → A.BishopComplex
toAnalytic z = A.bishop-complex (C.re z) (C.im z)

toSetoid : A.BishopComplex → C.BishopComplex
toSetoid z = C.complex (A.re z) (A.im z)

toAnalyticAfterSetoid : (z : A.BishopComplex) →
  toAnalytic (toSetoid z) ≡ z
toAnalyticAfterSetoid (A.bishop-complex x y) = refl

toSetoidAfterAnalytic : (z : C.BishopComplex) →
  toSetoid (toAnalytic z) ≡ z
toSetoidAfterAnalytic (C.complex x y) = refl

toAnalyticZero : toAnalytic C.zeroC ≡ A.zeroC
toAnalyticZero = refl

toAnalyticOne : toAnalytic C.oneC ≡ A.oneC
toAnalyticOne = refl

toAnalyticAdd : (x y : C.BishopComplex) →
  toAnalytic (C._+C_ x y) ≡
  A._+C_ (toAnalytic x) (toAnalytic y)
toAnalyticAdd (C.complex a b) (C.complex c d) = refl

toAnalyticMultiply : (x y : C.BishopComplex) →
  toAnalytic (C._*C_ x y) ≡
  A._*C_ (toAnalytic x) (toAnalytic y)
toAnalyticMultiply (C.complex a b) (C.complex c d) = refl

toAnalyticNegate : (x : C.BishopComplex) →
  toAnalytic (C.negC x) ≡
  A.negC (toAnalytic x)
toAnalyticNegate (C.complex a b) = refl

toAnalyticConjugate : (x : C.BishopComplex) →
  toAnalytic (C.conjugate x) ≡
  A.conjC (toAnalytic x)
toAnalyticConjugate (C.complex a b) = refl

-- This is the original already-constructed Bishop exponential on
-- the actual Riemann complex pair, not a fresh exp convergence axiom.
bishopAnalyticComplexExp :
  C.BishopSetoidComplexTranscendentals →
  A.BishopComplex → A.BishopComplex
bishopAnalyticComplexExp T z =
  toAnalytic (C.expC T (toSetoid z))

bishopAnalyticExpReal :
  (T : C.BishopSetoidComplexTranscendentals)
  (x y : R.ℝ) →
  A.re (bishopAnalyticComplexExp T (A.bishop-complex x y))
  ≡
  R._*_ (Exp.bishopExp x) (E.bishopCos (C.dataSet T) y)
bishopAnalyticExpReal T x y = refl

bishopAnalyticExpImag :
  (T : C.BishopSetoidComplexTranscendentals)
  (x y : R.ℝ) →
  A.im (bishopAnalyticComplexExp T (A.bishop-complex x y))
  ≡
  R._*_ (Exp.bishopExp x) (E.bishopSin (C.dataSet T) y)
bishopAnalyticExpImag T x y = refl

-- The original Bishop complex exp congruence is reused unchanged,
-- then projected to the Riemann's true analytic coordinates.
bishopAnalyticExpCongruent :
  (T : C.BishopSetoidComplexTranscendentals) →
  ∀ {x y : A.BishopComplex} →
  R._≃_ (A.re x) (A.re y) →
  R._≃_ (A.im x) (A.im y) →
  (R._≃_ (A.re (bishopAnalyticComplexExp T x))
           (A.re (bishopAnalyticComplexExp T y)))
  ×
  (R._≃_ (A.im (bishopAnalyticComplexExp T x))
           (A.im (bishopAnalyticComplexExp T y)))
bishopAnalyticExpCongruent T realSame imagSame =
  let equivalence =
        C.expCongruent T
          (C.complex-equivalent realSame imagSame)
  in
  C.reEquivalent equivalence
  ,
  C.imEquivalent equivalence
